"""Read-only service over retained artifact chains, independent of old sessions."""
import csv
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

from . import service as common, review_pages, source_edits, artifact_edits
from .publication import MAX_REVIEW_STATES
from .durable_artifact import Store, canonical, digest, require, running_tooling, UNSPECIFIED_BASE

HERE=Path(__file__).resolve().parent
from .rename_service import RenameService, neighbor_view

ERRORS='''REVIEW_SESSION_CHANGED REVIEW_PROFILE_INVALID REVIEW_RESTORE_IN_PROGRESS
    REVIEW_READ_ONLY MISSING_REVIEW_PROVENANCE INVALID_REVIEW_PROVENANCE
    REASSEMBLY_FAILED ARTIFACT_SCHEMA_UNSUPPORTED ARTIFACT_MANIFEST_MISMATCH
    ARTIFACT_UNIT_MISMATCH ARTIFACT_FILE_MISMATCH ARTIFACT_PROVENANCE_MISMATCH
    ARTIFACT_CAPTURE_MISMATCH ARTIFACT_BLOB_MISMATCH ARTIFACT_PATH_INVALID
    BASE_ARTIFACT_MISMATCH TOOLCHAIN_UNAVAILABLE DESTINATION_EXISTS
    REASSEMBLY_DEPENDENCY_INVALID REASSEMBLY_INPUT_OUTSIDE_TREE REVIEW_PASS_CONTEXT_MISSING'''.split()
common.PUBLIC_ERROR_CODES |= frozenset(ERRORS)


def check_reassembly_inputs(manifest,tree,source,executable,command):
    code='REASSEMBLY_DEPENDENCY_INVALID';tree=Path(tree).resolve()
    require(isinstance(manifest,dict) and manifest.get('schema')=='xasm-dependencies'
            and manifest.get('version')=='1',code)
    invocation=manifest.get('invocation',{})
    require(invocation.get('cwd')==str(source.parent) and invocation.get('argv')==command,code)
    entries=manifest.get('inputs');missing=manifest.get('missing_paths')
    require(isinstance(entries,list) and entries and isinstance(missing,list),code)
    seen=set();producers=0;sources=0
    for entry in entries:
        require(isinstance(entry,dict) and isinstance(entry.get('path'),str),code)
        path=Path(entry['path']);roles=entry.get('roles')
        require(path.is_absolute() and str(path) not in seen and isinstance(roles,list),code)
        seen.add(str(path))
        if 'producer' in roles:
            require(roles==['producer'] and path.resolve()==executable.resolve(),code);producers+=1
        else:
            require(path.resolve().is_relative_to(tree),'REASSEMBLY_INPUT_OUTSIDE_TREE')
            sources+=int(path.resolve()==source.resolve() and 'source' in roles)
        require(path.is_file() and path.stat().st_size==entry.get('size')
                and digest(path.read_bytes())==entry.get('sha256'),code)
    require(producers==1 and sources==1,code)
    for item in missing:
        require(isinstance(item,str) and Path(item).is_absolute(),code)
        require(Path(item).resolve().is_relative_to(tree),'REASSEMBLY_INPUT_OUTSIDE_TREE')
        require(not Path(item).exists(),code)
    return len(entries)-1


class RetainedReviewService(RenameService):
    @classmethod
    def from_publication(cls,root,store_root,artifact_id):
        from .publication import read_ticket
        ticket=read_ticket(store_root,artifact_id)
        return cls.create(root,store_root,ticket['artifacts'],ticket['producer_sha256'],ticket['profile'],
                          anchor_artifact=ticket.get('anchor_artifact'))

    @classmethod
    def create(cls,root,store_root,artifacts,producer_sha256,profile,*,anchor_artifact=None):
        root=Path(root).resolve();root.mkdir(parents=True,exist_ok=False)
        config={'schema':'retained-review-session-v2' if anchor_artifact else 'retained-review-session-v1',
            'store_root':str(Path(store_root).resolve()),'artifacts':artifacts,
            'producer_sha256':producer_sha256,'profile':profile}
        if anchor_artifact:config['anchor_artifact']=anchor_artifact
        common.write_json(root/'session.json',config)
        return cls(root)

    def __init__(self,root):
        self.root=Path(root).resolve();self.state_path=self.root/'state.json'
        self.config=json.loads((self.root/'session.json').read_text())
        common.schema(self.config,('schema','store_root','artifacts','producer_sha256','profile'),('anchor_artifact',))
        self.anchor=self.config.get('anchor_artifact')
        require(self.config['schema']==('retained-review-session-v2' if self.anchor else 'retained-review-session-v1'),
                'REVIEW_SESSION_CHANGED')
        require(self.config['profile'] in ('rename','source-v2','instruction'),'REVIEW_PROFILE_INVALID')
        require(isinstance(self.config['artifacts'],list) and 2<=len(self.config['artifacts'])<=MAX_REVIEW_STATES,
                'REVIEW_SESSION_CHANGED')
        require(len(set(self.config['artifacts']))==len(self.config['artifacts']),'BASE_ARTIFACT_MISMATCH')
        if self.anchor:require(self.anchor==self.config['artifacts'][0],'BASE_ARTIFACT_MISMATCH')
        sha=self.config['producer_sha256']
        require(isinstance(sha,str) and re.fullmatch('[0-9a-f]{64}',sha),'TOOLCHAIN_UNAVAILABLE')
        self.store=Store(self.config['store_root'])
        self.executable=self.store.root/'toolchains'/sha/'xasm'
        require(self.executable.is_file(),'TOOLCHAIN_UNAVAILABLE')
        self.runtime=running_tooling(self.executable)
        self.bodies={};previous=UNSPECIFIED_BASE if self.anchor else None
        for eid in self.config['artifacts']:
            body=self.store.open(eid,self.runtime,previous)
            if self.bodies:
                prior=self.bodies[previous]
                require(all(body[k]==prior[k] for k in ('source_path','reference_path','reference_sha256','tooling_id')),
                        'BASE_ARTIFACT_MISMATCH')
                require(isinstance(self.provenance(body),list) and self.provenance(body),
                        'MISSING_REVIEW_PROVENANCE')
            self.bodies[eid]=body;previous=eid
        require(self.bodies[previous].get('review_anchor')==self.anchor,'BASE_ARTIFACT_MISMATCH')
        if self.anchor:
            from .publication import read_ticket
            prior_ticket=read_ticket(self.store.root,self.anchor)
            require(prior_ticket['profile']==self.config['profile'],'REVIEW_PROFILE_INVALID')
        first=next(iter(self.bodies.values()))
        if self.config['profile']=='source-v2':
            registry=first['captures'].get('ownership.json')
            require(registry is not None and all(b['captures'].get('ownership.json')==registry for b in self.bodies.values()),'REVIEW_SESSION_CHANGED')
        self.review_pass_id=first.get('review_pass_id')
        if self.config['profile'] in ('rename','source-v2'):
            require(isinstance(self.review_pass_id,str) and self.review_pass_id.isdigit()
                    and all(b.get('review_pass_id')==self.review_pass_id for b in self.bodies.values()),
                    'REVIEW_PASS_CONTEXT_MISSING')
        self.source=first['source_path'];self.reference=first['reference_path']
        self.project='/'.join(Path(self.source).parts[:2])+'/'
        self.slug=Path(self.source).parts[1]
        self.cache={};self.fixture={}  # Review selection never consults an answer key.
        generations={};cache_root=self.root/'generations';cache_root.mkdir(exist_ok=True)
        with (self.root/'restore.lock').open('a+b') as lock:
            try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:raise ValueError('REVIEW_RESTORE_IN_PROGRESS') from None
            for eid,body in self.bodies.items():
                destination=cache_root/eid
                if not destination.exists():
                    with tempfile.TemporaryDirectory(prefix='.restore-',dir=cache_root) as temporary:
                        pending=Path(temporary)/'entry'
                        self.store.materialize(eid,self.runtime,pending,body['base_artifact'])
                        pending.replace(destination)
                generations[eid]={'checkout':str(destination/'project'),'capture':str(destination/'capture'),
                    'manifest':body['manifest'],'capture_hashes':body['captures'],
                    'base':body['base_artifact'],'provenance':self.provenance(body),
                    'content_id':body['content_id'],'tooling_id':body['tooling_id']}
            self._projection={'current':previous,'reference_sha256':first['reference_sha256'],
                              'generations':generations,'candidates':{}}
            if self.state_path.exists():
                require(json.loads(self.state_path.read_text())==self._projection,'REVIEW_SESSION_CHANGED')
            else:common.write_json(self.state_path,self._projection)
        self.reload()
        for eid in self.bodies:self.model(eid)

    def provenance(self,body):
        try:return json.loads(self.store.get(body['provenance'],'ARTIFACT_PROVENANCE_MISMATCH'))
        except (ValueError,TypeError):raise ValueError('ARTIFACT_PROVENANCE_MISMATCH') from None

    def document_pass_id(self):
        # A continued window has no restored ancestry before its anchor. The
        # publication receipt carries the original pass's scorecard scope.
        require(self.review_pass_id is not None,'REVIEW_PASS_CONTEXT_MISSING')
        return self.review_pass_id

    def reload(self):
        require(json.loads((self.root/'session.json').read_text())==self.config,'REVIEW_SESSION_CHANGED')
        state=json.loads(self.state_path.read_text())
        require(state==self._projection,'REVIEW_SESSION_CHANGED')
        self.state=state

    def save(self):raise ValueError('REVIEW_READ_ONLY')

    def readers(self):
        return common.reader_hashes()

    def evidence(self,generation):
        if generation not in self.bodies:raise ValueError('UNKNOWN_GENERATION')
        body=self.bodies[generation]
        return {'artifact_id':generation,'content_id':body['content_id'],'tooling_id':body['tooling_id']}

    @common.state_operation()
    def status(self,role='reviewer'):
        result={'generation':self.state['current'],'role':role,'mode':'retained-review',
                'evidence':[self.evidence(eid) for eid in self.bodies]}
        if self.anchor:result['review_window']=self.review_window()
        return result

    def review_window(self):
        return {'anchor_artifact':self.anchor,'previous_artifact':self.bodies[self.anchor]['base_artifact'],
                'scope':'Changes after this published anchor; earlier changes remain in its review ticket.'}

    def review_metadata(self,generation,base_generation):
        result={'evidence':{'before':self.evidence(base_generation),'after':self.evidence(generation)}}
        if self.anchor:result['review_window']=self.review_window()
        return result

    @common.state_operation()
    def review(self,generation,base_generation,offset=0,limit=1):
        review_pages.validate_pagination(offset,limit)
        if self.config['profile']=='instruction' and limit!=1:raise ValueError('invalid pagination')
        record=self.state['generations'].get(generation)
        if record is None:raise ValueError('UNKNOWN_GENERATION')
        if record['base']!=base_generation:raise ValueError('MIXED_GENERATION_COMPARISON')
        if not record['provenance']:raise ValueError('MISSING_REVIEW_PROVENANCE')
        if self.config['profile'] in ('rename','source-v2'):
            require(all(isinstance(op,dict) and op.get('kind') in
                        ({'rename','comment_replace','ledger_append','scorecard_update','closeout','document_write','document_delete'} | (source_edits.KINDS | artifact_edits.KINDS if self.config['profile']=='source-v2' else set()))
                        for op in record['provenance']),'INVALID_REVIEW_PROVENANCE')
            return RenameService.review(self,generation,base_generation,offset,limit)
        result=self.instruction_review(generation,base_generation,offset,limit)
        result.update(self.review_metadata(generation,base_generation))
        return review_pages.fit(result)

    def instruction_review(self,generation,base_generation,offset,limit):
        newer=self.model(generation);older=self.model(base_generation)
        record=self.state['generations'][generation];old=self.state['generations'][base_generation]
        changes=[]
        for item in record['provenance']:
            require(isinstance(item,dict) and set(item)=={'base_record_operation'},'INVALID_REVIEW_PROVENANCE')
            op=item['base_record_operation']
            require(isinstance(op,dict),'INVALID_REVIEW_PROVENANCE')
            if op.get('kind')=='replace_operand':
                node=newer.node(op['record_id'])
                bound=sorted({d for ref,d in newer.bindings.items() if newer.context(ref)==node},key=lambda n:newer.ranges[n])
                changes.append({'kind':'operand_replacement','record_id':op['record_id'],
                    'before':neighbor_view(older,older.node(op['record_id'])),
                    'after':neighbor_view(newer,node),
                    'bound_declarations':[neighbor_view(newer,d) for d in bound]})
            elif op.get('kind')=='add_constant':
                require(op.get('name') in newer.declarations,'INVALID_REVIEW_PROVENANCE')
                node=newer.declarations[op['name']]
                require(newer.ids[node] not in older.nodes,'INVALID_REVIEW_PROVENANCE')
                changes.append({'kind':'declaration_added','after':neighbor_view(newer,node),
                    'placement_anchor':{'before':older.statement(older.node(op['after'])),
                                        'after':newer.statement(newer.node(op['after']))}})
            else:raise ValueError('INVALID_REVIEW_PROVENANCE')
        catalog=self.project+'docs/reverse_engineering/inventory/constants_catalog.csv'
        if old['manifest'].get(catalog)!=record['manifest'].get(catalog):
            def rows(root):
                with (Path(root)/catalog).open() as stream:
                    return {r['constant_name']:r for r in csv.DictReader(stream)}
            before=rows(old['checkout']);after=rows(record['checkout'])
            changes.append({'kind':'generated_catalog','path':catalog,'rows':[
                {'name':name,'before':before.get(name),'after':after.get(name)}
                for name in sorted(before.keys()|after.keys()) if before.get(name)!=after.get(name)]})
        files=common.changed_file_views(old['manifest'],record['manifest'],self.project,self.source)
        return {'generation':generation,'base_generation':base_generation,'selection_basis':'edit_provenance',
                'review_code_hashes':self.readers(),'changes':changes[offset:offset+limit],
                'offset':offset,'total_changes':len(changes),
                'next_offset':offset+limit if offset+limit<len(changes) else None,'changed_files':files,
                'limits':['Stored instruction-edit provenance only; no arbitrary-history alignment or semantic verdict.']}

    @common.state_operation()
    def reassemble(self,generation):
        self.model(generation)
        body=self.bodies[generation];record=self.state['generations'][generation]
        require(digest(self.executable.read_bytes())==body['producer_sha256'],'TOOLCHAIN_UNAVAILABLE')
        source=Path(record['checkout'])/self.source
        env={'PATH':'/usr/bin:/bin','HOME':str(self.root),'TMPDIR':str(self.root),'LC_ALL':'C','LANG':'C'}
        started=time.monotonic()
        with tempfile.TemporaryDirectory(prefix='reassemble-',dir=self.root) as temporary:
            output=Path(temporary)/'out.bin'
            dependencies=Path(temporary)/'dependencies.json'
            command=[str(self.executable),'--pure-binary','--dependency-manifest='+str(dependencies),
                     '-o',str(output),str(source)]
            try:
                run=subprocess.run(command,
                    cwd=source.parent,env=env,capture_output=True,timeout=30)
            except (OSError,subprocess.SubprocessError):raise ValueError('REASSEMBLY_FAILED') from None
            require(run.returncode==0 and output.is_file(),'REASSEMBLY_FAILED')
            try:dependency_bytes=dependencies.read_bytes();manifest=json.loads(dependency_bytes)
            except (OSError,ValueError):raise ValueError('REASSEMBLY_DEPENDENCY_INVALID') from None
            input_count=check_reassembly_inputs(manifest,record['checkout'],source,self.executable,command)
            binary=output.read_bytes()
            reference,_=common.producer.read_ines(Path(record['checkout'])/self.reference)
            require(binary==reference,'ROM_PARITY')
        return {'generation':generation,'evidence':self.evidence(generation),
                'producer_sha256':body['producer_sha256'],'producer_location':'retained-toolchain',
                'reference_prg_parity':True,'output_sha256':digest(binary),'bytes':len(binary),
                'dependency_input_count':input_count,'dependency_inputs_inside_restored_tree':True,
                'dependency_manifest_sha256':digest(dependency_bytes),
                'seconds':time.monotonic()-started,'stderr_sha256':digest(run.stderr)}

    def dispatch(self,operation,arguments,role):
        if operation in ('propose','amend','validate','publish','preview','confirm','start_chain'):
            raise ValueError('REVIEW_READ_ONLY')
        specs={'evidence':(('generation','view'),('offset','limit','record_id','address','decoder','byte_offset','byte_count','artifact','analogue_index','key')),'status':((),()),'query':(('generation','symbol'),('offset','limit')),
               'review':(('generation','base_generation'),('offset','limit')),
               'reassemble':(('generation',),())}
        if self.config['profile'] in ('rename','source-v2'):
            specs.update(navigate=(('generation','view'),('symbol','record_id','contains','offset','limit')),inspect=(('generation','symbol'),()),q09=(('generation','names'),('offset','limit')),
                         document=(('generation','path'),('offset','limit')))
        if operation not in specs:raise ValueError('UNKNOWN_OPERATION')
        common.schema(arguments,*specs[operation])
        if operation=='status':return self.status(role)
        if operation=='evidence':return self.evidence_query(**arguments)
        return getattr(self,operation)(**arguments)
