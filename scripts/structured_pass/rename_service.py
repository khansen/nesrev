"""Bound rename, authored ledger and comment records on the common service.

Review selection is derived from edit provenance, never acceptance-fixture IDs.
Global/local declaration names and all reference bindings come from xasm.
"""
import csv
from bisect import bisect_left
import io
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
from . import service as common
from .model import Model, digest, producer, translated
from . import mixed_documents as mixed
from . import authored_documents as authored
from . import navigation, review_pages, source_edits, artifact_edits, evidence_views
FIELDS = ('old_name','new_name','reason','confidence','pass_id')
ERRORS = '''PREVIEW_REQUIRED UNKNOWN_PREVIEW STALE_PREVIEW PREVIEW_DIGEST_MISMATCH
    WRONG_DECLARATION_SCOPE INVALID_RENAME DUPLICATE_RENAME INVALID_COMMENT
    COMMENT_NOT_FOUND COMMENT_PREIMAGE_MISMATCH LEDGER_SCHEMA LEDGER_PREIMAGE_MISMATCH
    LEDGER_RENAME_MISMATCH UNDISPOSED_STALE_PROSE UNCHANGED_LEDGER_REQUIRED
    FORBIDDEN_PATH GENERATED_PATH_SERVICE_OWNED PREVIEW_ITEM_TOO_LARGE PREVIEW_CONTENT_CHANGED'''.split()
common.PUBLIC_ERROR_CODES = common.PUBLIC_ERROR_CODES | frozenset(ERRORS) | authored.ERRORS | navigation.ERRORS | source_edits.ERRORS | artifact_edits.ERRORS | evidence_views.ERRORS


def comments(model):
    result = [];offset = 0
    for i,unit in enumerate(model.units):
        data = bytes.fromhex(unit['hex'])
        if unit['kind']=='comment':
            encoding={}
            try:text=data.decode('utf-8')
            except UnicodeDecodeError:
                text=data.decode('utf-8','replace')
                encoding={'text_encoding':'utf-8-replacement','bytes_hex':data.hex()}
            result.append({'record_id':f'u{i}','kind':'comment','line':unit['line'],
                'column':unit['column'],'start':offset,'end':offset+len(data),
                'text':text,'preimage_sha256':digest(data),**encoding})
        offset += len(data)
    return result


def mentions(text, names):
    # A lexical prose check only; never used to discover code references.
    return [n for n in names if re.search(r'(?<![A-Za-z0-9_@])'+re.escape(n)+r'(?![A-Za-z0-9_@])',text)]


def name_range(model, declaration):
    d = model.declaration_records.get(declaration)
    if d is None or d['kind'] not in ('global','local','equ'):
        raise ValueError('INVALID_RENAME')
    return d['name_span']['byte_start'], d['name_span']['byte_end_exclusive']


def selected_renames(model, operations):
    result = [];seen = set();new_names = set()
    for op in operations:
        if op.get('kind')!='rename':
            continue
        common.schema(op,('kind','declaration_id','old_name','new_name','preimage'))
        n = model.node(op['declaration_id']);old = model.name(n);new = op['new_name']
        if old!=op['old_name']:
            raise ValueError('WRONG_DECLARATION_SCOPE')
        if model.statement(n)['preimage_sha256']!=op['preimage']:
            raise ValueError('PREIMAGE_MISMATCH')
        local = model.facts[n]['kind']=='LOCAL_LABEL_NODE'
        if not isinstance(new,str) or not re.fullmatch(r'@@[A-Za-z_][A-Za-z0-9_]*' if local else r'[A-Za-z_][A-Za-z0-9_]*',new) or new==old:
            raise ValueError('INVALID_RENAME')
        if n in seen or new in new_names or (not local and new in model.declarations):
            raise ValueError('DUPLICATE_RENAME')
        name_range(model,n)
        seen.add(n);new_names.add(new)
        result.append((op,n,[ref for ref,decl in model.bindings.items() if decl==n]))
    if not 0 <= len(result) <= 64 or not any(o.get('kind') in authored.KINDS | mixed.KINDS | source_edits.KINDS | artifact_edits.KINDS | {'rename','comment_replace'} for o in operations):
        raise ValueError('INVALID_RENAME')
    return result


def edits_for(model, operations, project):
    generated={project+n for n in common.GENERATED_RELATIVE}
    if not isinstance(operations,list) or not all(isinstance(o,dict) and isinstance(o.get('kind'),str) for o in operations):
        raise ValueError('REQUEST_SCHEMA')
    renames = selected_renames(model,operations);edits=list(source_edits.plan(model,operations)['edits'])
    for op,n,refs in renames:
        edits.append((*name_range(model,n),op['new_name'].encode()))
        edits.extend((*model.ranges[ref],op['new_name'].encode()) for ref in refs)
    comment_map = {c['record_id']:c for c in comments(model)};seen=set()
    for op in operations:
        kind = op.get('kind')
        if kind in ('rename','ledger_append') or kind in mixed.KINDS or kind in authored.KINDS or kind in source_edits.KINDS or kind in artifact_edits.KINDS:
            continue
        if kind=='comment_replace':
            common.schema(op,('kind','record_id','preimage','text','reason'))
            if not isinstance(op['record_id'],str):raise ValueError('REQUEST_SCHEMA')
            c = comment_map.get(op['record_id'])
            if c is None or op['record_id'] in seen:
                raise ValueError('COMMENT_NOT_FOUND')
            if op['preimage']!=c['preimage_sha256']:
                raise ValueError('COMMENT_PREIMAGE_MISMATCH')
            if not isinstance(op['text'],str) or not op['text'].startswith(';') or any(x in op['text'] for x in '\r\n') or not isinstance(op['reason'],str) or not op['reason'].strip():
                raise ValueError('INVALID_COMMENT')
            seen.add(op['record_id']);edits.append((c['start'],c['end'],op['text'].encode()))
        elif kind=='file_write':
            if op.get('path') in (project+mixed.SCORECARD,project+mixed.DEFERRALS):
                raise ValueError('MIXED_FILE_REQUIRES_TYPED_UPDATE')
            raise ValueError('GENERATED_PATH_SERVICE_OWNED' if op.get('path') in generated else 'FORBIDDEN_PATH')
        elif kind in ('deferral_update','deferral_append','deferral_delete'):
            raise ValueError('WRAPPER_OWNED_ROW')
        else:
            raise ValueError('UNSUPPORTED_OPERATION')
    edits.sort()
    if any(a[1]>b[0] or a[0]==a[1]==b[0] for a,b in zip(edits,edits[1:])):
        raise ValueError('OVERLAPPING_EDITS')
    data = model.source
    for lo,hi,replacement in reversed(edits):
        data = data[:lo]+replacement+data[hi:]
    return edits,data


def rename_pairs(operations,model=None):
    result=[]
    for op in operations:
        if op.get('kind')=='rename':result.append((op['old_name'],op['new_name']))
        elif op.get('kind')=='localize':
            if model is None:raise ValueError('LEDGER_RENAME_MISMATCH')
            result.append((model.name(model.node(op['declaration_id'])),op['new_name']))
    return result


def retired_names(operations,model):
    return [op['old_name'] for op in operations if op.get('kind')=='rename']+[
        model.name(model.node(op['declaration_id'])) for op in operations
        if op.get('kind') in ('localize','delete_declaration')]


def ledger_operation(operations, project, model=None):
    ledger=project+'docs/reverse_engineering/inventory/renames.csv'
    generated={project+n for n in common.GENERATED_RELATIVE}
    if not isinstance(operations,list) or not all(isinstance(op,dict) and isinstance(op.get('kind'),str) for op in operations):
        raise ValueError('REQUEST_SCHEMA')
    found = [op for op in operations if op.get('kind')=='ledger_append']
    if not found and not any(o.get('kind') in ('rename','localize') for o in operations) and any(o.get('kind') in authored.KINDS | mixed.KINDS | source_edits.KINDS | artifact_edits.KINDS | {'comment_replace'} for o in operations):
        return None
    if len(found)!=1:
        raise ValueError('LEDGER_SCHEMA')
    op, = found
    common.schema(op,('kind','path','preimage','rows'))
    if not isinstance(op['path'],str):raise ValueError('REQUEST_SCHEMA')
    if op['path']!=ledger:
        raise ValueError('GENERATED_PATH_SERVICE_OWNED' if op['path'] in generated else 'FORBIDDEN_PATH')
    if not isinstance(op['rows'],list) or not op['rows']:
        raise ValueError('LEDGER_SCHEMA')
    for row in op['rows']:
        common.schema(row,FIELDS)
        if any(not isinstance(row[k],str) or not row[k].strip() or '\n' in row[k] or '\r' in row[k] for k in FIELDS):
            raise ValueError('LEDGER_SCHEMA')
    expected = rename_pairs(operations,model)
    if [(r['old_name'],r['new_name']) for r in op['rows']]!=expected:
        raise ValueError('LEDGER_RENAME_MISMATCH')
    return op


def neighbor_view(model,node):
    lo,hi = model.ranges[node]
    if not hasattr(model,'_review_statements'):
        statements=sorted((model.ranges[n][0],n) for n,f in model.facts.items()
                          if f['kind'] in producer.CONTEXTS or f['kind'] in ('LABEL_NODE','LOCAL_LABEL_NODE'))
        model._review_statements=([offset for offset,n in statements],[n for offset,n in statements])
    offsets,nodes=model._review_statements
    left=bisect_left(offsets,lo);right=bisect_left(offsets,hi)
    before=nodes[max(0,left-2):left];after=nodes[right:right+2]
    return {'record':model.statement(node),'before':[model.statement(n) for n in before],
            'after':[model.statement(n) for n in after]}


def use_view(older,newer,reference_id,declaration_id):
    """Full changed statements and bound leaves; neighbours are an explicit read."""
    sides={}
    for side,model in (('before',older),('after',newer)):
        ref=model.node(reference_id);node=model.context(ref);owner=model.owners[node]
        sides[side]={'record':model.statement(node),'reference':model.expression(ref),
                     'lexical_owner_id':model.ids[owner] if owner is not None else None}
    return {'kind':'rename_use','declaration_id':declaration_id,'reference_id':reference_id,
            **sides,'neighbors_omitted':True}


def use_pages(older,newer,op,base_generation):
    # Cache only page boundaries on the already integrity-checked model. No
    # persisted facts/IDs or provenance change when the review layout changes.
    key=(base_generation,op['declaration_id'],tuple(op['reference_ids']))
    cache=getattr(newer,'_review_use_pages',None)
    if cache is None:newer._review_use_pages=cache={}
    if key not in cache:
        pages=[];rows=[];refs=[]
        for ref in op['reference_ids']:
            row=use_view(older,newer,ref,op['declaration_id'])
            if refs and (len(refs)==8 or review_pages.wire_size({'changes':rows+[row]})>review_pages.BUDGET-4096):
                pages.append(refs);rows=[];refs=[]
            rows.append(row);refs.append(ref)
        if refs:pages.append(refs)
        cache[key]=pages
    return cache[key]


class RenameService(common.Service):
    review_profile='source-v2'

    def publication_pass_id(self):
        return self.document_pass_id()
    @classmethod
    def readers(cls):
        return common.reader_hashes()

    @property
    def ledger(self):
        return self.project+'docs/reverse_engineering/inventory/renames.csv'

    @property
    def generated(self):
        return {self.project+n for n in common.GENERATED_RELATIVE}

    def plan(self, model, operations, test_rename=False):
        if not isinstance(operations,list) or not all(isinstance(op,dict) for op in operations):
            raise ValueError('REQUEST_SCHEMA')
        edits,data = edits_for(model,operations,self.project)
        ledger_operation(operations,self.project,model)
        mixed.document_operations(operations)
        artifact_edits.operations(operations)
        authored.selected(operations,self.project,self.source,self.ownership)
        return edits,data

    def document_pass_id(self):
        generation=self.state['current']
        while self.state['generations'][generation]['base'] is not None:
            generation=self.state['generations'][generation]['base']
        self.model(generation)
        root=Path(self.state['generations'][generation]['checkout'])/self.project
        rows=mixed.Scorecard((root/mixed.SCORECARD).read_bytes()).rows
        return str(max((int(pid) for pid in rows if pid.isdigit()),default=0)+1)

    @common.state_operation()
    def documents(self,generation):
        self.model(generation)
        root=Path(self.state['generations'][generation]['checkout'])/self.project
        scorecard=(root/mixed.SCORECARD).read_bytes();deferrals=(root/mixed.DEFERRALS).read_bytes()
        parsed=mixed.Scorecard(scorecard)
        pass_id=self.document_pass_id()
        current={pass_id:parsed.rows[pass_id]} if pass_id in parsed.rows else {}
        return {'generation':generation,'pass_id':pass_id,
                'scorecard':{'path':self.project+mixed.SCORECARD,'preimage':digest(scorecard),
                    'rows':current,'history_rows_omitted':len(parsed.rows)-len(current),
                    'wrapper_owned_fields':sorted(mixed.PROTECTED)},
                'deferrals':{'path':self.project+mixed.DEFERRALS,'preimage':digest(deferrals),
                    'rows':mixed.deferral_rows(deferrals),'writer':'project_pass_closeout.sh'}}

    def check_authored(self,generation,operations):
        record=self.state['generations'][generation]
        authored.prepare(record['checkout'],record['manifest'],operations,self.project,self.source,self.ownership)
        if mixed.document_operations(operations) is None:return
        root=Path(self.state['generations'][generation]['checkout'])/self.project
        return mixed.prepare((root/mixed.SCORECARD).read_bytes(),(root/mixed.DEFERRALS).read_bytes(),
                             operations,self.document_pass_id())

    @common.state_operation()
    def navigate(self,generation,view,**selection):
        return {'generation':generation,**navigation.Navigation(self.model(generation)).query(view,**selection)}

    @common.state_operation()
    def inspect(self, generation, symbol):
        m = self.model(generation)
        if symbol not in m.declarations:
            raise ValueError('unknown constant')
        n = m.declarations[symbol]
        return {'generation':generation,'declaration':neighbor_view(m,n),
            'use_count':sum(d==n for d in m.bindings.values()),
            'ledger':{'path':self.ledger,'sha256':self.state['generations'][generation]['manifest'][self.ledger]}}

    def q09_report(self, generation, names):
        # Complete internal inventory: preview must never check only a read page.
        if not isinstance(names,list) or len(names)>64 or any(not isinstance(n,str) or not n for n in names):
            raise ValueError('REQUEST_SCHEMA')
        model = self.model(generation);record=self.state['generations'][generation]
        result = [{'kind':'comment','record':c,'mentions':mentions(c['text'],names)}
                  for c in comments(model) if mentions(c['text'],names)]
        for path in sorted(record['manifest']):
            artifact_kind=next((k for k,p in artifact_edits.PATHS.items() if path==self.project+p),None)
            if not path.casefold().endswith('.md') and artifact_kind is None or self.ownership(path,self.project,self.source)=='handoff-owned':
                continue
            data=(Path(record['checkout'])/path).read_bytes()
            lines=(artifact_edits.current_lines(data,artifact_kind) if artifact_kind else mixed.current_prose_lines(data,self.document_pass_id())
                   if path.casefold()==(self.project+mixed.SCORECARD).casefold()
                   else enumerate(data.decode().splitlines(),1))
            for number,line in lines:
                matched = mentions(line,names)
                if matched:result.append({'kind':'authored_prose','path':path,'line':number,'text':line,'mentions':matched})
        return {'generation':generation,'mentions':result,
                'exclusions':['Historical review archives, prior scorecard rows and rename-ledger old_name entries remain history.'],
                'scope':'Source comment units, admitted typed artifacts and current tracked project Markdown; current scorecard row and non-row prose remain checked.'}

    @common.state_operation()
    def q09(self,generation,names,offset=0,limit=12):
        if type(offset) is not int or offset<0 or type(limit) is not int or not 1<=limit<=40:
            raise ValueError('REQUEST_SCHEMA')
        report=self.q09_report(generation,names);hits=report.pop('mentions')
        result={**report,'mentions':[],'offset':offset,'limit':limit,'total_mentions':len(hits),'next_offset':None}
        for hit in hits[offset:offset+limit]:
            trial={**result,'mentions':result['mentions']+[hit]}
            if review_pages.wire_size(trial)>review_pages.BUDGET-4096:
                if result['mentions']:break
                raise common.ServiceError('RESPONSE_TOO_LARGE',offset=offset,total_mentions=len(hits),
                    action=f'One prose match exceeds the response budget and was not delivered. Inspect its document or comment record; read Q09 at offset {offset+1} to continue past it.',
                    match={k:hit[k] for k in ('kind','path','line') if k in hit} |
                          ({'record_id':hit['record']['record_id']} if 'record' in hit else {}))
            result['mentions'].append(hit)
        end=offset+len(result['mentions'])
        result['next_offset']=end if end<len(hits) else None
        return result

    @common.state_operation(write=True)
    def preview(self, generation, operations, cid=None, role='implementer'):
        if role!='implementer':raise ValueError('REVIEWER_MUTATION_DENIED')
        if generation!=self.state['current']:raise ValueError('STALE_GENERATION')
        m = self.model(generation);self.plan(m,operations)
        ledger = ledger_operation(operations,self.project,m)
        if ledger is not None and ledger['preimage']!=self.state['generations'][generation]['manifest'][self.ledger]:
            raise ValueError('LEDGER_PREIMAGE_MISMATCH')
        documents=self.check_authored(generation,operations)
        names=retired_names(operations,m)
        prose=self.q09_report(generation,names)
        record=self.state['generations'][generation]
        authored_changes=authored.prepare(record['checkout'],record['manifest'],operations,self.project,self.source,self.ownership)
        artifact_changes=artifact_edits.prepare(Path(record['checkout']),record['manifest'],operations,self.project,authored_changes)
        artifact_text={item['path']:(item['after'] if item['after'] is not None else artifact_edits.preview_warning(m,item['op'],operations)) for item in artifact_changes}
        doc_ops={o['path']:o for o in authored.selected(operations,self.project,self.source,self.ownership)}
        for hit in prose['mentions']:
            if hit['kind']=='authored_prose' and hit['path'] not in self.generated:
                if hit['path'].casefold()==(self.project+mixed.SCORECARD).casefold() and documents is not None:
                    if any(mentions(line,names) for _,line in mixed.current_prose_lines(documents['data'],self.document_pass_id())):
                        raise common.ServiceError('UNDISPOSED_STALE_PROSE',paths=[hit['path']])
                    continue
                if hit['path'] in artifact_text:
                    if mentions(artifact_text[hit['path']].decode(),names):raise common.ServiceError('UNDISPOSED_STALE_PROSE',paths=[hit['path']])
                    continue
                replacement=doc_ops.get(hit['path'])
                if replacement is None or mentions(replacement.get('text',''),names):
                    raise common.ServiceError('UNDISPOSED_STALE_PROSE',paths=[hit['path']])
        record=self.state['generations'][generation]
        doc_changes=authored.prepare(record['checkout'],record['manifest'],operations,self.project,self.source,self.ownership)
        stale_paths=[item['path'] for item in doc_changes if item['after'] is not None and mentions(item['after'].decode(),names)]
        if stale_paths:raise common.ServiceError('UNDISPOSED_STALE_PROSE',paths=stale_paths)
        revision = None
        if cid is not None:
            c = self.candidate(cid)
            if c['status']=='validating':raise ValueError('CANDIDATE_NOT_AMENDABLE')
            if c['status']=='published' or c['base']!=generation:raise ValueError('STALE_PREVIEW')
            revision = c['revision']
        identity = {'generation':generation,'candidate':cid,'revision':revision,'operations':operations}
        token = digest(json.dumps(identity,sort_keys=True).encode())
        details = {'generation':generation,'candidate':cid,'revision':revision,'preview_digest':token,
            'renames':[{'declaration_id':m.ids[n],'old_name':op['old_name'],'new_name':op['new_name'],
                        'declaration':neighbor_view(m,n),
                        'uses':[{'reference_id':m.ids[r],'owner':m.statement(m.context(r)).get('lexical_owner'),
                                 'record':m.statement(m.context(r))} for r in refs]}
                       for op,n,refs in selected_renames(m,operations)],
            'q09':prose,'authored_ledger_rows':ledger['rows'] if ledger else [],
            'authored_documents':[authored.describe(item) for item in doc_changes],
            'comment_dispositions':[op for op in operations if op['kind']=='comment_replace'],
            'source_edits':source_edits.previews(m,operations),
            'artifact_edits':artifact_edits.operations(operations),
            'mixed_documents':None if documents is None else {
                'scorecard_before':documents['before'],'scorecard_draft':documents['draft'],
                'wrapper_owned_fields':sorted(mixed.PROTECTED),
                'closeout_request':documents['closeout'],
                'writer':'project_pass_closeout.sh',
                'deferral_keys':'Generated by the wrapper; existing rows remain unchanged.'}}

        from .paging import preview_records,page
        records=preview_records(details)
        first_page=page(records)
        # Check all items before registering an actionable confirmation token.
        for item in records:page([item])
        payload=json.dumps(records,sort_keys=True).encode()
        directory=self.root/'previews';directory.mkdir(exist_ok=True)
        (directory/(token+'.json')).write_bytes(payload)
        self.state.setdefault('previews',{})[token]=identity
        self.state.setdefault('preview_outputs',{})[token]=digest(payload)
        self.save()
        return {'generation':generation,'candidate':cid,'revision':revision,'preview_digest':token,
                'summary':{'renames':len(details['renames']),'comments':len(details['comment_dispositions']),
                           'documents':len(details['authored_documents'])},**first_page}

    @common.state_operation()
    def preview_page(self,generation,preview_digest,offset=0,limit=12):
        from .paging import page
        if generation!=self.state['current']:raise ValueError('STALE_GENERATION')
        if preview_digest not in self.state.get('previews',{}):raise ValueError('UNKNOWN_PREVIEW')
        raw=(self.root/'previews'/(preview_digest+'.json')).read_bytes()
        if digest(raw)!=self.state.get('preview_outputs',{}).get(preview_digest):raise ValueError('PREVIEW_CONTENT_CHANGED')
        return {'generation':generation,'preview_digest':preview_digest,**page(json.loads(raw),offset,limit)}

    @common.state_operation(write=True)
    def confirm(self, generation, preview_digest, role='implementer'):
        if role!='implementer':raise ValueError('REVIEWER_MUTATION_DENIED')
        p = self.state.get('previews',{}).get(preview_digest)
        if p is None:raise ValueError('UNKNOWN_PREVIEW')
        if digest(json.dumps(p,sort_keys=True).encode())!=preview_digest:raise ValueError('PREVIEW_DIGEST_MISMATCH')
        if generation!=self.state['current'] or p['generation']!=generation:raise ValueError('STALE_PREVIEW')
        self.model(generation)
        if p['candidate'] is None:
            result = super().propose(generation,p['operations'],role)
        else:
            c = self.candidate(p['candidate'])
            if c['status']=='validating':raise ValueError('CANDIDATE_NOT_AMENDABLE')
            if c['revision']!=p['revision'] or c['status']=='published':raise ValueError('STALE_PREVIEW')
            self.clear_validation(p['candidate'])
            c.update(operations=p['operations'],revision=c['revision']+1,status='draft',attempt=0)
            self.save()
            result={'generation':generation,'base_generation':generation,'candidate':p['candidate'],
                    'revision':c['revision'],'status':'draft'}
        del self.state['previews'][preview_digest];self.save()
        return {**result,'confirmed_preview_digest':preview_digest}

    def apply_authored(self, checkout, operations):
        op = ledger_operation(operations,self.project,self.model(self.state['current']))
        if op is not None:
            path=checkout/self.ledger;data=path.read_bytes()
            if digest(data)!=op['preimage']:raise ValueError('LEDGER_PREIMAGE_MISMATCH')
            reader=csv.DictReader(io.StringIO(data.decode()))
            if tuple(reader.fieldnames)!=FIELDS:raise ValueError('LEDGER_SCHEMA')
            stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=FIELDS,lineterminator='\n');writer.writerows(op['rows'])
            path.write_bytes(data+(b'' if data.endswith(b'\n') else b'\n')+stream.getvalue().encode())
        record=self.state['generations'][self.state['current']]
        documents=authored.prepare(checkout,record['manifest'],operations,self.project,self.source,self.ownership)
        for item in artifact_edits.prepare(checkout,record['manifest'],operations,self.project,documents):
            if item['after'] is not None:
                target=checkout/item['path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(item['after'])
        for item in documents:
            target=checkout/item['path']
            if item['after'] is None:target.unlink()
            else:
                target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(item['after'])
        if mixed.document_operations(operations) is not None:
            root=checkout/self.project
            prepared=mixed.prepare((root/mixed.SCORECARD).read_bytes(),(root/mixed.DEFERRALS).read_bytes(),
                                   operations,self.document_pass_id())
            (root/mixed.SCORECARD).write_bytes(prepared['data'])

    def run_gates(self,checkout,operations,folder,env):
        if mixed.document_operations(operations) is None:
            return super().run_gates(checkout,operations,folder,env)
        return mixed.run_closeout(checkout,self.project,self.slug,operations,self.document_pass_id(),
                                  folder,env,checkout/'scripts')

    def after_certification(self,checkout,changed,operations):
        if any(op['kind']=='warning_baseline' for op in operations):
            record=self.state['generations'][self.state['current']]
            before=authored.read(record['checkout'],record['manifest'],self.project+artifact_edits.PATHS['warning_baseline'])
            artifact_edits.warnings(checkout,changed,operations,self.project,self.model(self.state['current']),before)
        artifact_edits.extents(checkout,changed,operations,self.project)

    def properties(self, base, changed, operations):
        edits,_=edits_for(base,operations,self.project if self else 'projects/sample/')
        p=source_edits.reconcile(base,changed,operations,edits) if any(op['kind'] in source_edits.KINDS for op in operations) else source_edits.plan(base,[])
        renamed=selected_renames(base,operations);selected={n for _,n,_ in renamed}
        result={'declarations_renamed':True,'every_bound_use_preserved':True,'unselected_bindings_preserved':True,
                'unselected_declarations_preserved':True,'reference_inventory_preserved':True,
                'no_stale_source_prose':True,'passed':False}
        for op,n,refs in renamed:
            newer=changed.nodes.get(base.ids[n])
            result['declarations_renamed'] &= newer is not None and changed.name(newer)==op['new_name']
            for ref in refs:
                nr=changed.nodes.get(base.ids[ref]);bound=changed.bindings.get(nr)
                result['every_bound_use_preserved'] &= (bound is not None and changed.ids[bound]==base.ids[n]
                                                       and changed.facts[nr]['name']==op['new_name'])
        for ref,decl in base.bindings.items():
            if decl in selected or ref in p['removed']|p['replaced']:continue
            nr=changed.nodes.get(base.ids[ref]);nd=changed.bindings.get(nr)
            result['unselected_bindings_preserved'] &= nd is not None and changed.ids[nd]==base.ids[decl]
        for n,f in base.facts.items():
            if n not in selected|p['removed']|p['localized'] and f['kind'] in ('LABEL_NODE','LOCAL_LABEL_NODE','EQU_NODE'):
                newer=changed.nodes.get(base.ids[n])
                result['unselected_declarations_preserved'] &= newer is not None and changed.name(newer)==base.name(n)
        result['reference_inventory_preserved']=(
            {base.ids[r] for r in base.bindings}=={changed.ids[r] for r in changed.bindings}
            if not p['intents'] and not p['removed'] else
            source_edits.reference_inventory(base,changed,p,edits))
        names=retired_names(operations,base)
        result['no_stale_source_prose']=not any(mentions(c['text'],names) for c in comments(changed))
        result['passed']=all(v for k,v in result.items() if k!='passed')
        return result

    def manifest_paths(self, base, operations):
        paths=set(base['manifest'])
        paths.update(self.project+artifact_edits.PATHS[o['kind']] for o in artifact_edits.operations(operations))
        for op in authored.selected(operations,self.project,self.source,self.ownership):
            if op['kind']=='document_write':paths.add(op['path'])
            else:paths.remove(op['path'])
        return sorted(paths)

    def inventory_result(self, checkout, changed, operations):
        model=self.model(self.state['current'])
        op=ledger_operation(operations,self.project,model)
        if op is not None:
            with (checkout/self.ledger).open() as stream:rows=list(csv.DictReader(stream))
            if rows[-len(op['rows']):]!=op['rows']:raise ValueError('LEDGER_RENAME_MISMATCH')
        base=self.state['generations'][self.state['current']]
        expected=set(self.manifest_paths(base,operations))
        changed_paths={p for p in expected|base['manifest'].keys()
                       if (producer.sha(checkout/p) if (checkout/p).is_file() else None)!=base['manifest'].get(p)}
        allowed={self.source,self.ledger}|self.generated|{o['path'] for o in authored.selected(operations,self.project,self.source,self.ownership)}
        if mixed.document_operations(operations) is not None:
            allowed|={self.project+mixed.SCORECARD,self.project+mixed.DEFERRALS}
        allowed|={self.project+artifact_edits.PATHS[o['kind']] for o in artifact_edits.operations(operations)}
        raw_ram=self.project+artifact_edits.RAW_RAM_PATH
        if raw_ram in changed_paths:
            artifact_edits.raw_ram_changes(
                authored.read(base['checkout'],base['manifest'],raw_ram),
                (checkout/raw_ram).read_bytes() if (checkout/raw_ram).is_file() else None)
            allowed.add(raw_ram)
        if not changed_paths<=allowed:raise common.ServiceError('FORBIDDEN_PATH',paths=sorted(changed_paths-allowed))
        names=retired_names(operations,model)
        for p in expected:
            kind=next((k for k,path in artifact_edits.PATHS.items() if p==self.project+path),None)
            if kind is not None:
                if any(mentions(line,names) for _,line in artifact_edits.current_lines((checkout/p).read_bytes(),kind)):
                    raise common.ServiceError('UNDISPOSED_STALE_PROSE',paths=[p])
            if not p.casefold().endswith('.md') or self.ownership(p,self.project,self.source) in ('handoff-owned','generated'):
                continue
            data=(checkout/p).read_bytes()
            lines=(mixed.current_prose_lines(data,self.document_pass_id())
                   if p.casefold()==(self.project+mixed.SCORECARD).casefold()
                   else enumerate(data.decode().splitlines(),1))
            if any(mentions(line,names) for _,line in lines):raise common.ServiceError('UNDISPOSED_STALE_PROSE',paths=[p])
        return {'authored_ledger_rows':len(op['rows']) if op else 0,'inventory_gates':'refreshed and verified'}

    @common.state_operation()
    def document(self,generation,path,offset=0,limit=80):
        if type(offset) is not int or offset<0 or type(limit) is not int or not 1<=limit<=80:raise ValueError('REQUEST_SCHEMA')
        self.model(generation);record=self.state['generations'][generation]
        authored.path_allowed(path,self.project,self.source,self.ownership)
        data=authored.read(record['checkout'],record['manifest'],path)
        lines=data.decode().splitlines() if data is not None else []
        return {'generation':generation,'path':path,'ownership':'authored','preimage':authored.sha(data),
                'exists':data is not None,'offset':offset,'lines':lines[offset:offset+limit],
                'total_lines':len(lines),'next_offset':offset+limit if offset+limit<len(lines) else None}

    def provenance(self, base, changed, operations):
        renames={op['declaration_id']:{'kind':'rename','declaration_id':base.ids[n],
                    'reference_ids':[base.ids[r] for r in refs],'old_name':op['old_name'],'new_name':op['new_name']}
                 for op,n,refs in selected_renames(base,operations)}
        return [renames[op['declaration_id']] if op['kind']=='rename' else op for op in operations]

    def review_metadata(self, generation, base_generation):
        return {}

    @common.state_operation()
    def review(self, generation, base_generation, offset=0, limit=1):
        review_pages.validate_pagination(offset,limit)
        newer=self.model(generation);older=self.model(base_generation);record=self.state['generations'][generation]
        old_record=self.state['generations'][base_generation]
        if record['base']!=base_generation:raise ValueError('MIXED_GENERATION_COMPARISON')
        # Flatten only identities up front. Materialize context for the requested
        # page, so reviewing N uses does not rebuild all N comparisons N times.
        items=[]
        edit_map=None
        for operation_index,op in enumerate(record['provenance']):
            if op['kind'] in artifact_edits.KINDS:
                path=self.project+artifact_edits.PATHS[op['kind']]
                before=authored.read(old_record['checkout'],old_record['manifest'],path)
                after=authored.read(record['checkout'],record['manifest'],path)
                rows=(artifact_edits.warning_changes(before,after,older,newer) if op['kind']=='warning_baseline'
                      else artifact_edits.changes(before,after,op))
                items.extend({'kind':'artifact_change','operation_kind':op['kind'],'path':path,
                    'reason':op['reason'],'row_offset':i,'total_rows':len(rows),
                    'before_sha256':old_record['manifest'].get(path),'after_sha256':record['manifest'][path],
                    'row':row} for i,row in enumerate(rows or [None]));continue
            if op['kind'] in source_edits.KINDS:
                if edit_map is None:edit_map=json.loads((Path(record['capture'])/'source-edit-map.json').read_text())['changes']
                items.extend(row for row in edit_map if row['operation_index']==operation_index);continue
            if op['kind']=='ledger_append':
                with (Path(old_record['checkout'])/self.ledger).open() as f:before=list(csv.DictReader(f))
                with (Path(record['checkout'])/self.ledger).open() as f:after=list(csv.DictReader(f))
                if after[:len(before)]!=before:raise ValueError('UNCHANGED_LEDGER_REQUIRED')
                added=after[len(before):]
                if added!=op['rows']:raise ValueError('LEDGER_RENAME_MISMATCH')
                items.extend({'kind':'authored_ledger','path':self.ledger,'unchanged_prefix_rows':len(before),
                              'row_offset':row_offset,'total_added_rows':len(added),'added_rows':rows}
                             for row_offset,rows in review_pages.ledger_pages(added))
                continue
            items.append(op)
            if op['kind']=='rename':
                items.extend({'kind':'rename_uses','declaration_id':op['declaration_id'],'reference_ids':refs}
                             for refs in use_pages(older,newer,op,base_generation))
        raw_ram=self.project+artifact_edits.RAW_RAM_PATH
        if old_record['manifest'].get(raw_ram)!=record['manifest'].get(raw_ram):
            rows=artifact_edits.raw_ram_changes(
                authored.read(old_record['checkout'],old_record['manifest'],raw_ram),
                authored.read(record['checkout'],record['manifest'],raw_ram))
            items.extend({'kind':'artifact_change','operation_kind':'raw_ram_refresh','path':raw_ram,
                          'ownership':'refresh-generated','row_offset':i,'total_rows':len(rows),
                          'before_sha256':old_record['manifest'].get(raw_ram),
                          'after_sha256':record['manifest'].get(raw_ram),'row':row}
                         for i,row in enumerate(rows))
        def groups():
            for op in items[offset-1:offset-1+limit]:
                changes=[]
                if op['kind']=='rename':
                    decl=op['declaration_id']
                    changes.append({'kind':'rename','declaration_id':decl,
                        'before':neighbor_view(older,older.node(decl)),'after':neighbor_view(newer,newer.node(decl)),
                        'use_count':len(op['reference_ids'])})
                elif op['kind']=='rename_uses':
                    changes.extend(use_view(older,newer,ref,op['declaration_id']) for ref in op['reference_ids'])
                elif op['kind']=='comment_replace':
                    before=next(c for c in comments(older) if c['record_id']==op['record_id'])
                    # The stored operations provide the origin; find the changed
                    # producer comment at its translated byte position, not by text.
                    all_ops=[]
                    for item in record['provenance']:
                        if item['kind']=='rename':
                            all_ops.append({'kind':'rename','declaration_id':item['declaration_id'],
                                'old_name':item['old_name'],'new_name':item['new_name'],
                                'preimage':older.statement(older.node(item['declaration_id']))['preimage_sha256']})
                        else:all_ops.append(item)
                    edits,_=edits_for(older,all_ops,self.project);position=translated(before['start'],edits,True)
                    after=next(c for c in comments(newer) if c['start']==position)
                    changes.append({'kind':'comment','before':before,'after':after,'reason':op['reason']})
                elif op['kind'] in ('authored_ledger','source_change','artifact_change'):
                    changes.append(op)
                elif op['kind'] in authored.KINDS:
                    before=authored.read(old_record['checkout'],old_record['manifest'],op['path'])
                    after=authored.read(record['checkout'],record['manifest'],op['path'])
                    changes.append(authored.describe({'path':op['path'],'before':before,'after':after,'reason':op['reason']}))
                elif op['kind']=='scorecard_update':
                    before=mixed.Scorecard((Path(old_record['checkout'])/self.project/mixed.SCORECARD).read_bytes())
                    after=mixed.Scorecard((Path(record['checkout'])/self.project/mixed.SCORECARD).read_bytes())
                    changes.append({'kind':'mixed_scorecard','path':self.project+mixed.SCORECARD,
                        'authored_fields':op['fields'],'before':before.rows.get(op['pass_id']),
                        'after':after.rows[op['pass_id']],'wrapper_owned_fields':sorted(mixed.PROTECTED)})
                elif op['kind']=='closeout':
                    receipt_bytes=(Path(record['capture'])/'closeout.json').read_bytes()
                    receipt=json.loads(receipt_bytes)
                    hashes=receipt.pop('wrapper_code_hashes')
                    receipt['wrapper_code_sha256']=digest(json.dumps(hashes,sort_keys=True,separators=(',',':')).encode())
                    receipt['wrapper_code_files']=len(hashes)
                    changes.append({'kind':'wrapper_closeout','receipt_sha256':digest(receipt_bytes),'receipt':receipt})
                yield changes
        files=common.changed_file_views(old_record['manifest'],record['manifest'],self.project,self.source,self.ownership)
        readers=self.readers()
        result={'generation':generation,'base_generation':base_generation,'selection_basis':'edit_provenance',
                'review_code_sha256':digest(json.dumps(readers,sort_keys=True,separators=(',',':')).encode()),
                'changes':[],'total_changes':sum(len(op['reference_ids']) if op['kind']=='rename_uses' else 1 for op in items),
                'total_pages':len(items)+1,'offset':offset,
                'page_kind':'metadata' if offset==0 else 'change',
                'next_offset':1 if offset==0 and items else None,
                'limits':['Shows stored edit provenance for supported operations; arbitrary history alignment is not implemented.']}
        if offset==0:
            result['review_code_hashes']=readers
            result['changed_files']=files
            names=[o['old_name'] for o in record['provenance'] if o['kind']=='rename']
            prose=self.q09_report(generation,names)
            result['q09']={k:v for k,v in prose.items() if k!='mentions'} | {
                'total_mentions':len(prose['mentions']),
                'read':{'operation':'q09','arguments':{'generation':generation,'names':names,'offset':0,'limit':12}}}
        result.update(self.review_metadata(generation,base_generation))
        return review_pages.pack(result,groups(),limit)

    @common.state_operation()
    def evidence_query(self,generation,view,offset=0,limit=40,**arguments):
        model=self.model(generation)
        analogue=arguments.pop('analogue_index',None)
        if analogue is not None:
            if view not in ('ram','outgoing','data','decode','scopes','units','expression'):raise ValueError('EVIDENCE_REQUEST_INVALID')
            from .analogue_inputs import project
            model=project(model,analogue)
            return {'generation':generation,'analogue_index':analogue,**evidence_views.query(model,view,offset,limit,**arguments)}
        if view=='prior_reuse':
            common.schema(arguments,('record_id',))
            from .analogue_inputs import rows
            return {'generation':generation,**evidence_views.page(rows(model,arguments['record_id']),offset,limit)}
        if view=='policy':
            common.schema(arguments,())
            path=model.capture/'gate-results.json'
            rows=json.loads(path.read_text()) if path.exists() else []
            return {'generation':generation,'available':path.exists(),
                    'meaning':'Recorded wrapper outcomes; naming, comment value and maturity still require review.',
                    **evidence_views.page(rows,offset,limit)}
        if view=='artifact_rows':
            common.schema(arguments,('artifact',),('key',))
            kind=arguments['artifact']
            if kind not in artifact_edits.PATHS:raise ValueError('EVIDENCE_REQUEST_INVALID')
            path=self.project+artifact_edits.PATHS[kind];record=self.state['generations'][generation]
            data=authored.read(record['checkout'],record['manifest'],path)
            rows=artifact_edits.entries(data,kind)
            key=arguments.get('key')
            if key is not None:
                if not isinstance(key,str):raise ValueError('EVIDENCE_REQUEST_INVALID')
                rows={k:r for k,r in rows.items() if k==key}
            fields=[{'key':k,'field':field,'value':value,'row_preimage':artifact_edits.row_hash(row)}
                    for k,row in rows.items() for field,value in row.items()]
            return {'generation':generation,'path':path,'preimage':authored.sha(data),'total_rows':len(rows),
                    **evidence_views.page(fields,offset,limit)}
        return {'generation':generation,**evidence_views.query(model,view,offset,limit,**arguments)}

    def dispatch(self, operation, arguments, role):
        if operation in ('propose','amend'):raise ValueError('PREVIEW_REQUIRED')
        spec={'evidence':(('generation','view'),('offset','limit','record_id','address','decoder','byte_offset','byte_count','artifact','analogue_index','key')),'preview_page':(('generation','preview_digest'),('offset','limit')),'navigate':(('generation','view'),('symbol','record_id','contains','offset','limit')),
              'inspect':(('generation','symbol'),()),'q09':(('generation','names'),('offset','limit')),
              'documents':(('generation',),()),'document':(('generation','path'),('offset','limit')),
              'review':(('generation','base_generation'),('offset','limit')),
              'preview':(('generation','operations'),('cid',)),'confirm':(('generation','preview_digest'),())}
        if operation in spec:
            common.schema(arguments,*spec[operation])
            if operation=='evidence':return self.evidence_query(**arguments)
            if operation in ('preview','confirm'):arguments=dict(arguments,role=role)
            return getattr(self,operation)(**arguments)
        return super().dispatch(operation,arguments,role)


def all_review_pages(service, generation, base):
    pages=[];offset=0
    while offset is not None:
        page=service.review(generation,base,offset)
        pages.append(page);offset=page['next_offset']
    return {'generation':generation,'base_generation':base,'selection_basis':'edit_provenance',
            'changes':[change for page in pages for change in page['changes']],
            'changed_files':pages[0]['changed_files'],'q09':pages[0]['q09'],'pages':pages}
