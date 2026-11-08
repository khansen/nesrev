"""Generation lifecycle owned by the trusted service outside the agent.

Source facts and edit spans come from the pinned assembler.
Client requests never select host commands or executables.
"""
import csv
import copy
from contextlib import contextmanager
import fcntl
from functools import wraps
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from .model import Model, certify, digest, producer
from .q04_view import constant_uses
from . import mixed_documents
from . import gate_environment
from . import gate_diagnostics
from . import ownership
HERE = Path(__file__).resolve().parent
GENERATED_RELATIVE = {'docs/reverse_engineering/inventory/'+name for name in
             ('constants_catalog.csv','pointer_targets.csv','embedded_pointer_targets.csv',
              'split_pointer_targets.csv','branch_literal_sites.csv','unknowns.md')}
REVISION_FIELDS = frozenset((
    'error','error_details','error_records','retryable','checkout','capture','certification_seconds','certification',
    'semantic_properties','gates','manifest','capture_hashes','edit_provenance',
    'generated_catalog_row','total_validation_seconds'))
PUBLIC_ERROR_CODES = producer.ERRORS | mixed_documents.ERRORS | gate_environment.ERRORS | frozenset('''
RESPONSE_TOO_LARGE OWNERSHIP_MANIFEST_INVALID STALE_VALIDATION_EVIDENCE
    INTERNAL_SERVICE_ERROR UNKNOWN_RECORD RECORD_ALIGNMENT_FAILED REFERENCE_INVALID REFERENCE_FORMAT_UNSUPPORTED
    CAPTURE_CHANGED INVALID_SYMBOL REQUEST_SCHEMA UNSUPPORTED_EXPRESSION
    INVALID_BATCH MULTI_RECORD_SELECTION_UNSUPPORTED GENERATED_PATH_SERVICE_OWNED
    FILE_WRITES_NOT_ENABLED_IN_THIS_CASE DECLARATION_ANCHOR_REQUIRED
    PREIMAGE_MISMATCH DUPLICATE_DECLARATION SINGLE_OPERAND_INSTRUCTION_REQUIRED
    UNSUPPORTED_OPERATION OVERLAPPING_EDITS UNKNOWN_GENERATION REFERENCE_CHANGED
    GENERATION_INPUT_CHANGED CAPTURE_SOURCE_MISMATCH REVIEWER_MUTATION_DENIED
    STALE_GENERATION CANDIDATE_NOT_AMENDABLE INVALID_AMENDMENT
    CANDIDATE_NOT_VALIDATABLE SEMANTIC_CONTRACT
    NONZERO_BASE_REQUIRES_DIAGNOSTIC_COMPARISON NEW_GATE_FAILURE
    GENERATED_CATALOG_WRONG CANDIDATE_NOT_PUBLISHABLE
    CANDIDATE_CHANGED_AFTER_VALIDATION MIXED_GENERATION_COMPARISON
    UNKNOWN_OPERATION UNKNOWN_CANDIDATE CANDIDATE_SETUP_FAILED ROM_PARITY
    VALIDATION_INTERRUPTED VALIDATION_IN_PROGRESS INSUFFICIENT_DISK_SPACE
    TOOLING_IDENTITY_MISMATCH RUNTIME_PROFILE_MISMATCH
    RETENTION_NOT_CONFIGURED ARTIFACT_EXPORT_FAILED RETENTION_PATH_INVALID
    PUBLICATION_RECEIPT_MISMATCH TOOLCHAIN_UNAVAILABLE
    PUBLICATION_CHAIN_LIMIT
    CHAIN_REQUIRES_PUBLISHED_BASE
'''.split())


class ServiceError(ValueError):
    def __init__(self, code, **details):
        super().__init__(code)
        self.details = details


def file_ownership(path, project, source, registered=()):
    if not isinstance(path,str) or not path.casefold().startswith(project.casefold()):raise ValueError('REQUEST_SCHEMA')
    if path.casefold()==source.casefold():return 'source'
    relative=path[len(project):].casefold()
    if relative.startswith('docs/reverse_engineering/reviews/'):return 'handoff-owned'
    if relative in {name.casefold() for name in GENERATED_RELATIVE}:return 'generated'
    if relative in {name.casefold() for name in (mixed_documents.SCORECARD,mixed_documents.DEFERRALS,
                    'docs/reverse_engineering/inventory/raw_ram_review.csv')}:return 'mixed'
    if relative=='pass_edits.jsonl':return 'service-owned'
    if relative=='project.conf' or relative.startswith(('reference/','mods/')):return 'forbidden'
    typed={p.casefold():owner for p,owner in ownership.TYPED.items()}
    if relative in typed:return typed[relative]
    if relative.startswith('docs/reverse_engineering/inventory/pass/'):return 'generated-pass-cache'
    if relative in {p.casefold() for p in ownership.DOCUMENTS | set(registered)}:return 'authored'
    return 'forbidden'


def changed_file_views(before,after,project,source, classifier=file_ownership):
    return [{'path':path,'ownership':classifier(path,project,source),
             'before_sha256':before.get(path),'after_sha256':after.get(path)}
            for path in sorted(before.keys()|after.keys()) if before.get(path)!=after.get(path)]


def public_error_code(error, fallback='INTERNAL_SERVICE_ERROR'):
    if not isinstance(error,ValueError):
        return fallback
    message = str(error)
    if message in PUBLIC_ERROR_CODES:
        return message
    return {'invalid pagination':'INVALID_PAGINATION','unknown constant':'UNKNOWN_CONSTANT',
            'unknown record ID':'UNKNOWN_RECORD'}.get(message,fallback)


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix+'.new')
    temporary.write_text(json.dumps(value,indent=2)+'\n')
    temporary.replace(path)


def state_operation(write=False):
    def decorate(method):
        @wraps(method)
        def call(self,*args,**kwargs):
            with self.transaction(write=write):
                return method(self,*args,**kwargs)
        return call
    return decorate


def git(root, *args, env=None):
    return subprocess.check_output(['/usr/bin/git', *args],cwd=root,env=env,stderr=subprocess.PIPE).decode().strip()


def reader_hashes():
    return {p.name:producer.sha(p) for p in sorted(HERE.glob('*.py'))} | {
        'source-model.schema.json':producer.sha(HERE/'source-model.schema.json'),
        'nes_graphics.py':producer.sha(Path(producer.rom.__file__))} | {
        name:producer.sha(HERE.parent/name) for name in ('data_blob_dispositions_check.py',
            'runtime_evidence_check.py','data_format_targets_check.py')}


def capture_hashes(capture):
    # These are integrity receipts, not the input-derived generation identity.
    return {p.name:producer.sha(p) for p in sorted(Path(capture).iterdir()) if p.is_file()}


def check_capture(record):
    if capture_hashes(record['capture']) != record['capture_hashes']:
        raise ValueError('CAPTURE_CHANGED')


def name(value):
    if not isinstance(value,str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',value):
        raise ValueError('INVALID_SYMBOL')
    return value


def schema(value, keys, optional=()):
    if not isinstance(value,dict) or not set(keys)<=set(value) or not set(value)<=set(keys)|set(optional):
        raise ValueError('REQUEST_SCHEMA')


def expression(value):
    if set(value)=={'symbol'}:
        return name(value['symbol']).encode()
    if set(value)=={'integer'} and type(value['integer']) is int and 0<=value['integer']<=65535:
        return str(value['integer']).encode()
    raise ValueError('UNSUPPORTED_EXPRESSION')




class Service:
    source = reference = project = slug = None
    fixture_path = baseline_path = None
    minimum_free_bytes = 2 * 1024**3
    authored_paths = ()
    analogue_models = ()

    def ownership(self,path,project,source):
        record=self.state['generations'][self.state['current']]
        manifest=Path(record['capture'])/'ownership.json'
        expected=record['capture_hashes'].get('ownership.json')
        if (producer.sha(manifest) if manifest.is_file() else None)!=expected:
            raise ValueError('CAPTURE_CHANGED')
        paths=ownership.read(json.loads(manifest.read_text())) if manifest.exists() else ()
        return file_ownership(path,project,source,paths)

    @classmethod
    def readers(cls):
        return reader_hashes()

    def __init__(self, state_root):
        self.root = Path(state_root).resolve()
        self.state_path = self.root/'state.json'
        self.state = json.loads(self.state_path.read_text())
        self.fixture = json.loads(self.fixture_path.read_text())
        self.cache = {}
        if (producer.sha(producer.EXE)!=self.state['producer_sha256'] or
                self.readers()!=self.state['reader_hashes']):
            raise ValueError('RUNTIME_PROFILE_MISMATCH')
        self.recover_interrupted()

    def recover_interrupted(self):
        try:
            with self.transaction(write=True):
                pass  # Recovery belongs to every outer write, including startup.
        except ValueError as error:
            if str(error)!='VALIDATION_IN_PROGRESS':raise

    def recover_locked(self):
        changed = False
        for cid,candidate in self.state['candidates'].items():
            if candidate['status']=='validating':
                self.clear_validation(cid)
                candidate.update(status='rejected',error='VALIDATION_INTERRUPTED',retryable=True)
                changed = True
        if changed:self.save()

    def reload(self):
        self.state = json.loads(self.state_path.read_text())

    @contextmanager
    def transaction(self,write=False):
        if getattr(self,'_operation_active',False):
            if write and not self._write_locked:
                raise RuntimeError('STATE_WRITE_IN_READ_OPERATION')
            yield
            return
        lock = None
        try:
            if write:
                lock = (self.root/'validation.lock').open('a+b')
                try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
                except BlockingIOError:raise ValueError('VALIDATION_IN_PROGRESS') from None
            # State files are atomically replaced; readers can take a consistent
            # snapshot while a validator owns the write lock.
            self.reload()
            self._operation_active = True
            self._write_locked = write
            # No validator can still own a record while we hold this lock.
            if write:self.recover_locked()
            yield
        finally:
            self._operation_active = False
            self._write_locked = False
            if lock is not None:lock.close()

    @classmethod
    def initialize(cls, state_root, base_checkout, base_capture, clone_seed, *, retention_root=None):
        from .publication import configuration
        root = Path(state_root).resolve();root.mkdir(parents=True)
        toolchain=gate_environment.configure(producer.EXE,root/'gate-home')
        environment=gate_environment.environment(toolchain,root/'gate-tmp')
        base = Path(base_checkout).resolve()
        # Keep caller-supplied and historical captures immutable. The new
        # session's registry travels with every retained capture and its hashes.
        bootstrap=root/'bootstrap-capture'
        shutil.copytree(base_capture,bootstrap)
        write_json(bootstrap/'ownership.json',ownership.registry(cls.authored_paths))
        from . import analogue_inputs
        analogue_inputs.capture(list(cls.analogue_models),bootstrap)
        base_capture=bootstrap
        model = Model(base_capture)
        fixture = json.loads(cls.fixture_path.read_text())
        if digest(model.source)!=fixture['source_sha256']:
            raise ValueError('CAPTURE_SOURCE_MISMATCH')
        paths = git(base,'ls-files',cls.project,env=environment).splitlines()
        manifest = {p:producer.sha(base/p) for p in paths}
        identity = {'files':manifest,'producer':producer.sha(producer.EXE),'readers':cls.readers(),
                    'reference':producer.sha(base/cls.reference),
                    'ownership':producer.sha(bootstrap/'ownership.json'),
                    'analogues':producer.sha(bootstrap/'analogues.json')}
        generation = 'G-'+digest(json.dumps(identity,sort_keys=True).encode())[:20]
        state = {'producer_sha256':producer.sha(producer.EXE),'current':generation,
                 'pass_start_generation':generation,'gate_toolchain':toolchain,
                 'retention':configuration(identity['producer'],retention_root),
                 'reader_hashes':cls.readers(),'reference_sha256':producer.sha(base/cls.reference),
                 'clone_seed':str(Path(clone_seed).resolve()),'paths':paths,
                 'base_gate_results':json.loads(cls.baseline_path.read_text()),
                 'generations':{generation:{'checkout':str(base),'capture':str(Path(base_capture).resolve()),
                     'capture_hashes':capture_hashes(base_capture),'manifest':manifest,'base':None}},
                 'candidates':{}}
        write_json(root/'state.json',state)
        return cls(root)

    def save(self):
        if not getattr(self,'_write_locked',False):
            raise RuntimeError('STATE_WRITE_REQUIRES_LOCK')
        write_json(self.state_path,self.state)

    def clear_validation(self, cid):
        candidate = self.candidate(cid)
        for field in REVISION_FIELDS:
            candidate.pop(field,None)
        self.cache.pop(cid,None)

    @state_operation()
    def candidate(self, cid):
        if not isinstance(cid,str):raise ValueError('REQUEST_SCHEMA')
        if cid not in self.state['candidates']:
            raise ValueError('UNKNOWN_CANDIDATE')
        return self.state['candidates'][cid]

    def plan(self, model, operations, test_rename=False):
        raise ValueError('UNSUPPORTED_OPERATION')

    def apply_authored(self, checkout, operations):
        pass

    def check_authored(self, generation, operations):
        pass

    def after_certification(self,checkout,changed,operations):
        pass

    def run_gates(self, checkout, operations, folder, env):
        gates=[]
        for target in ('project-inventory','project-verify','project-process-check','project-docs-check'):
            started=time.monotonic();log=folder/(target+'.log')
            with log.open('wb') as stream:
                result=subprocess.run([self.state['gate_toolchain']['executables']['make'],target,'PROJECT='+self.slug],cwd=checkout,env=env,
                                      stdout=stream,stderr=subprocess.STDOUT)
            gates.append({'target':target,'exit_code':result.returncode,
                          'seconds':time.monotonic()-started,'log_sha256':producer.sha(log),'environment':dict(env)})
        return gates

    def properties(self, base, changed, operations):
        raise ValueError('UNSUPPORTED_OPERATION')

    def provenance(self, base, changed, operations):
        return [{'base_record_operation':op} for op in operations]

    def manifest_paths(self, base, operations):
        return sorted(base["manifest"])

    def inventory_result(self, checkout, changed, operations):
        raise ValueError('UNSUPPORTED_OPERATION')

    @state_operation()
    def model(self, generation):
        if generation not in self.state['generations']:
            raise ValueError('UNKNOWN_GENERATION')
        record = self.state['generations'][generation]
        checkout = Path(record['checkout'])
        if producer.sha(checkout/self.reference)!=self.state['reference_sha256']:
            raise ValueError('REFERENCE_CHANGED')
        # Re-check files whose identities underwrite every response.
        if any(producer.sha(checkout/p)!=h for p,h in record['manifest'].items()):
            raise ValueError('GENERATION_INPUT_CHANGED')
        check_capture(record)
        if generation not in self.cache:
            self.cache[generation] = Model(record['capture'])
        if digest(self.cache[generation].source)!=record['manifest'][self.source]:
            raise ValueError('CAPTURE_SOURCE_MISMATCH')
        return self.cache[generation]

    @state_operation()
    def query(self, generation, symbol, offset=0, limit=20):
        return {'generation':generation,**constant_uses(self.model(generation),symbol,offset,limit)}

    @state_operation(write=True)
    def propose(self, generation, operations, role='implementer', *, test_rename=False):
        if role!='implementer':
            raise ValueError('REVIEWER_MUTATION_DENIED')
        if generation!=self.state['current']:
            raise ValueError('STALE_GENERATION')
        model = self.model(generation)
        edits,data = self.plan(model,operations,test_rename)
        self.check_authored(generation,operations)
        cid = f'C{len(self.state["candidates"])+1}'
        self.state['candidates'][cid] = {'base':generation,'operations':operations,'status':'draft','revision':0,
                                        'test_only_mutation':test_rename}
        self.save()
        return {'generation':generation,'candidate':cid,'revision':0,'status':'draft',
                'changed_ranges':len(edits),'source_sha256':digest(data)}

    @state_operation(write=True)
    def amend(self, cid, replacements, role='implementer'):
        candidate = self.candidate(cid)
        if role!='implementer':
            raise ValueError('REVIEWER_MUTATION_DENIED')
        if candidate['status'] in ('validating','published','discarded') or candidate['base']!=self.state['current']:
            raise ValueError('CANDIDATE_NOT_AMENDABLE')
        operations = list(candidate['operations'])
        for change in replacements:
            schema(change,('index','operation'))
            if type(change['index']) is not int or not 0<=change['index']<len(operations):
                raise ValueError('INVALID_AMENDMENT')
            operations[change['index']] = change['operation']
        self.plan(self.model(candidate['base']),operations)
        self.check_authored(candidate['base'],operations)
        self.clear_validation(cid)
        candidate.update(operations=operations,status='draft',revision=candidate['revision']+1,attempt=0)
        self.save()
        return {'generation':candidate['base'],'candidate':cid,'revision':candidate['revision'],'status':'draft'}

    @state_operation(write=True)
    def validate(self, cid, role='implementer'):
        return self._validate(cid,role)

    def _validate(self, cid, role='implementer'):
        c = self.candidate(cid)
        if role!='implementer':
            raise ValueError('REVIEWER_MUTATION_DENIED')
        retry_setup = (c['status']=='rejected' and c.get('error') in ('CANDIDATE_SETUP_FAILED','VALIDATION_INTERRUPTED')
                       and c.get('retryable') is True)
        if (c['status']!='draft' and not retry_setup) or c['base']!=self.state['current']:
            raise ValueError('CANDIDATE_NOT_VALIDATABLE')
        if shutil.disk_usage(self.root).free < self.minimum_free_bytes:
            raise ValueError('INSUFFICIENT_DISK_SPACE')
        self.clear_validation(cid)
        c.update(status='validating',attempt=c.get('attempt',0)+1)
        self.save()
        started = time.monotonic()
        folder = self.root/cid/str(c['revision'])/str(c['attempt'])
        checkout = folder/'checkout';capture = folder/'capture'
        phase = 'setup'
        try:
            folder.mkdir(parents=True)
            env=gate_environment.environment(self.state['gate_toolchain'],folder/'gate-tmp')
            subprocess.run([self.state['gate_toolchain']['executables']['git'],'clone','--quiet','--shared','--no-checkout',self.state['clone_seed'],str(checkout)],check=True,env=env)
            git(checkout,'checkout','--detach',self.fixture['base_commit'],env=env)
            # Keep the pinned tooling, but materialize the complete project
            # state from this candidate's certified base, including prior edits.
            base = self.model(c['base'])
            base_record = self.state['generations'][c['base']]
            # A previous document deletion must not be resurrected from the clone seed.
            for path in set(self.state['paths'])-base_record['manifest'].keys():
                destination=checkout/path
                if destination.exists():destination.unlink()
            for path,expected in base_record['manifest'].items():
                destination = checkout/path
                destination.parent.mkdir(parents=True,exist_ok=True)
                shutil.copy2(Path(base_record['checkout'])/path,destination)
                if producer.sha(destination)!=expected:
                    raise ValueError('GENERATION_INPUT_CHANGED')
            ref = checkout/self.reference;ref.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(Path(base_record['checkout'])/self.reference,ref)
            edits,data = self.plan(base,c['operations'],c['test_only_mutation'])
            (checkout/self.source).write_bytes(data)
            self.apply_authored(checkout,c['operations'])
            c.update(checkout=str(checkout),capture=str(capture))
            self.save()
            phase = 'certification'
            t = time.monotonic()
            # New record IDs must not depend on temporary candidate numbering:
            # equal generation inputs across sessions must expose equal IDs.
            id_seed = {'base':c['base'],'operations':c['operations'],'source':digest(data)}
            prefix = 'edit-'+digest(json.dumps(id_seed,sort_keys=True).encode())[:20]
            changed,certification = certify(checkout/self.source,capture,ref,base,edits,prefix=prefix)
            for retained in ['ownership.json','analogues.json',*(p.name for p in base.capture.glob('analogue-*.json.gz'))]:
                shutil.copy2(base.capture/retained,capture/retained)
            c['certification_seconds'] = time.monotonic()-t
            c['certification'] = certification
            phase = 'acceptance'
            properties = self.properties(base,changed,c['operations'])
            c['semantic_properties'] = properties
            if not properties['passed']:
                raise ValueError('SEMANTIC_CONTRACT')
            self.after_certification(checkout,changed,c['operations'])
            gates = self.run_gates(checkout,c['operations'],folder,env)
            failure_count=sum(bool(gate['exit_code']) for gate in gates)
            for gate in gates:
                if gate['exit_code']:
                    gate['diagnostic']=gate_diagnostics.explanation(folder/(gate['target']+'.log'),checkout,self.source,changed,
                        max_output=gate_diagnostics.MAX_OUTPUT//failure_count)
            c['gates'] = gates
            # The baseline gates must be green. Never turn a nonzero baseline
            # into a blanket allowance for different or masked downstream errors.
            if any(g['exit_code'] for g in self.state['base_gate_results']['checks']):
                raise ValueError('NONZERO_BASE_REQUIRES_DIAGNOSTIC_COMPARISON')
            if any(g['exit_code'] for g in gates):
                raise ValueError('NEW_GATE_FAILURE')
            write_json(capture/'gate-results.json',[{k:g[k] for k in ('target','exit_code','seconds','log_sha256')} for g in gates])
            inventory = self.inventory_result(checkout,changed,c['operations'])
            manifest = {p:producer.sha(checkout/p) for p in self.manifest_paths(base_record,c['operations'])}
            c.update(status='validated',manifest=manifest,
                     capture_hashes=capture_hashes(capture),
                     edit_provenance=self.provenance(base,changed,c['operations']),
                     generated_catalog_row=inventory)
            self.cache[cid] = changed
        except Exception as error:
            if isinstance(error, ServiceError):
                c['error_details'] = dict(error.details)
                if 'records' in c['error_details']:
                    c['error_records']=c['error_details'].pop('records')
                    c['error_details'].update(total_records=len(c['error_records']),read={
                        'operation':'validation_evidence','arguments':{'cid':cid,'revision':c['revision'],'attempt':c['attempt']}})
            # Raw producer logs stay service-owned; clients get a bounded code.
            fallback = 'INTERNAL_SERVICE_ERROR'
            retryable = phase=='setup' and isinstance(error,(OSError,subprocess.SubprocessError))
            c.update(status='rejected',retryable=retryable,
                     error='CANDIDATE_SETUP_FAILED' if retryable else public_error_code(error,fallback))
            try:
                if folder.is_dir():
                    (folder/'validation-error.txt').write_text(type(error).__name__+': '+str(error)+'\n')
            except OSError:
                pass  # Diagnostics cannot prevent the rejection from being saved.
        c['total_validation_seconds'] = time.monotonic()-started
        self.save()
        return {'generation':self.state['current'],'base_generation':c['base'],'candidate':cid,
                'revision':c['revision'],'attempt':c['attempt'],'status':c['status'],
                'error':c.get('error'),'error_details':c.get('error_details'),'retryable':c.get('retryable',False),
                'semantic_properties':c.get('semantic_properties'),
                'reference_prg_parity':c.get('certification',{}).get('reference_prg_parity'),
                'gates':c.get('gates',[]),'total_validation_seconds':c['total_validation_seconds']}

    @state_operation(write=True)
    def publish(self, cid, role='implementer'):
        c = self.candidate(cid)
        if role!='implementer':
            raise ValueError('REVIEWER_MUTATION_DENIED')
        if c['status']=='published' and 'review' in c:
            return self.published_response(cid,c)
        if c['status']!='validated' or c['base']!=self.state['current']:
            raise ValueError('CANDIDATE_NOT_PUBLISHABLE')
        checkout = Path(c['checkout'])
        if any(producer.sha(checkout/p)!=h for p,h in c['manifest'].items()):
            raise ValueError('CANDIDATE_CHANGED_AFTER_VALIDATION')
        check_capture(c)
        identity = {'files':c['manifest'],'producer':self.state['producer_sha256'],
                    'readers':self.state['reader_hashes'],'reference':self.state['reference_sha256'],
                    'provenance':c['edit_provenance'],'base':c['base']}
        generation = 'G-'+digest(json.dumps(identity,sort_keys=True).encode())[:20]
        staged=copy.deepcopy(self.state)
        staged['generations'][generation] = {'checkout':c['checkout'],'capture':c['capture'],
            'capture_hashes':c['capture_hashes'],'manifest':c['manifest'],
            'base':c['base'],'provenance':c['edit_provenance']}
        # Retain the complete chain before current/status can become published.
        # An interrupted export may leave immutable blobs, never a published
        # candidate without a review. Repeating export is safe.
        from .publication import export_chain
        try:
            review=export_chain(staged,generation,self.source,self.reference,self.review_profile,
                                review_pass_id=self.publication_pass_id())
        except OSError:
            raise ValueError('ARTIFACT_EXPORT_FAILED') from None
        staged['current']=generation
        staged['candidates'][cid].update(status='published',generation=generation,review=review)
        self.state=staged
        try:self.save()
        except Exception:
            self.reload()
            raise
        return self.published_response(cid,self.state['candidates'][cid])

    review_profile='instruction'

    def publication_pass_id(self):
        return None

    @state_operation(write=True)
    def start_chain(self,generation,role='implementer'):
        if role!='implementer':raise ValueError('REVIEWER_MUTATION_DENIED')
        if generation!=self.state['current']:raise ValueError('STALE_GENERATION')
        record=self.state['generations'][generation];saved=record.get('artifact')
        if not saved:raise ValueError('CHAIN_REQUIRES_PUBLISHED_BASE')
        from .publication import read_ticket
        from .durable_artifact import Store,running_tooling,require
        config=self.state['retention'];store=Store(config['root'])
        executable=store.root/'toolchains'/self.state['producer_sha256']/'xasm'
        ticket=read_ticket(store.root,saved['artifact_id'])
        body=store.open(saved['artifact_id'],running_tooling(executable))
        require(ticket['profile']==self.review_profile and body['legacy_generation']==generation
                and body['manifest']==record['manifest'],'PUBLICATION_RECEIPT_MISMATCH')
        self.model(generation)
        anchor={'generation':generation,'artifact_id':saved['artifact_id']}
        staged=copy.deepcopy(self.state);staged['chain_anchor']=anchor
        self.state=staged
        try:self.save()
        except Exception:
            self.reload();raise
        return {'generation':generation,'status':'chain_started','anchor_artifact':saved['artifact_id'],
                'content_id':body['content_id'],'tooling_id':body['tooling_id']}

    def published_response(self,cid,c):
        return {'generation':c['generation'],'previous_generation':c['base'],'candidate':cid,
                'revision':c['revision'],'status':'published','review':c['review']}

    @state_operation()
    def validation_evidence(self,cid,revision,attempt,offset=0,limit=40):
        from .evidence_views import page
        c=self.candidate(cid)
        if type(revision) is not int or type(attempt) is not int or revision!=c['revision'] or attempt!=c.get('attempt'):
            raise ValueError('STALE_VALIDATION_EVIDENCE')
        if 'error_records' not in c:raise ValueError('EVIDENCE_UNAVAILABLE')
        return {'candidate':cid,'revision':revision,'attempt':attempt,'error':c.get('error'),
                **page(c['error_records'],offset,limit)}

    @state_operation()
    def candidate_status(self,cid):
        c=self.candidate(cid)
        return {'generation':self.state['current'],'candidate':cid,'revision':c['revision'],
                'base_generation':c['base'],'status':c['status'],'error':c.get('error'),
                'error_details':c.get('error_details'),'retryable':c.get('retryable',False),'gates':c.get('gates',[]),
                'semantic_properties':c.get('semantic_properties'),
                'reference_prg_parity':c.get('certification',{}).get('reference_prg_parity')}

    @state_operation()
    def status(self,role='implementer'):
        result={'generation':self.state['current'],'role':role}
        if 'chain_anchor' in self.state:result['chain_anchor']=self.state['chain_anchor']
        return result

    @state_operation()
    def error_context(self,cid=None):
        result = {'generation':self.state['current']}
        if cid in self.state['candidates']:
            c = self.state['candidates'][cid]
            result.update(candidate=cid,revision=c['revision'],base_generation=c['base'])
        return result

    def dispatch(self, operation, arguments, role):
        allowed = {
            'validation_evidence':(('cid','revision','attempt'),('offset','limit')),
            'candidate_status':(('cid',),()),
            'query':(('generation','symbol'),('offset','limit')),
            'propose':(('generation','operations'),()),
            'amend':(('cid','replacements'),()),
            'validate':(('cid',),()),'publish':(('cid',),()),
            'start_chain':(('generation',),()),
            'review':(('generation','base_generation'),())}
        if operation=='status':
            schema(arguments,())
            return self.status(role)
        if operation not in allowed:
            raise ValueError('UNKNOWN_OPERATION')
        schema(arguments,*allowed[operation])
        if operation in ('propose','amend','validate','publish','start_chain'):
            arguments = dict(arguments,role=role)
        return getattr(self,operation)(**arguments)
