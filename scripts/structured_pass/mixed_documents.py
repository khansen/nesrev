"""Typed authored scorecard input and wrapper-only closeout results.

This parses Markdown/CSV document structure only. No assembler facts are inferred.
All existing deferral rows are protected; this slice supports wrapper append only.
"""
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import time
from . import gate_environment
SCORECARD = 'docs/reverse_engineering/PROGRESS_SCORECARD.md'
DEFERRALS = 'docs/reverse_engineering/inventory/deferrals.csv'
GATE_FIELDS = frozenset(('verify', 'docs_check', 'rework_items'))
SYNCED_FIELDS = frozenset(('labels_remaining','raw_rom_calls_remaining',
                         'raw_indirect_operands_remaining','hardcoded_counter_sites_remaining'))
UNMEASURED_FIELDS = frozenset(('warnings_baseline_delta','raw_ptr_immediates_remaining'))
AUTHORED = frozenset(('focus','notes'))
PROTECTED = GATE_FIELDS | SYNCED_FIELDS | UNMEASURED_FIELDS
UNMEASURED = 'not measured'
KINDS = frozenset(('scorecard_update', 'closeout'))
ERRORS = frozenset('''MIXED_DOCUMENT_SCHEMA MIXED_DOCUMENT_PREIMAGE
    WRAPPER_OWNED_FIELD WRAPPER_OWNED_ROW MIXED_FILE_REQUIRES_TYPED_UPDATE
    DOCUMENT_PASS_MISMATCH CLOSEOUT_REQUIRED CLOSEOUT_RESULT_INVALID
    CLOSEOUT_TOOLING_CHANGED DEFERRAL_ROW_CONFLICT'''.split())
DEFERRAL_FIELDS = ('pass_id','corridor','subject','kind','deferral','revisit_condition','status')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, code='MIXED_DOCUMENT_SCHEMA'):
    if not condition:
        raise ValueError(code)


def schema(value, fields):
    require(isinstance(value, dict) and set(value) == set(fields))


def cell(value):
    require(isinstance(value,str) and value.strip() and not any(c in value for c in '|\0\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029'))
    require(len(value) <= 8192)
    return value.strip()


class Scorecard:
    def __init__(self, data):
        self.lines = data.decode('utf-8').splitlines(keepends=True)
        self.rows = {};self.positions = {};self.header = None;self.header_line = None
        for index,line in enumerate(self.lines):
            stripped = line.strip()
            if not (stripped.startswith('|') and stripped.endswith('|')):
                continue
            cells = [c.strip() for c in stripped[1:-1].split('|')]
            if {'pass_id',*AUTHORED,*GATE_FIELDS} <= set(cells):
                require((self.header is None or cells == self.header) and len(cells) == len(set(cells)))
                require(set(cells)<=PROTECTED|AUTHORED|{'pass_id'})
                self.header = cells;self.header_line = index
                continue
            if self.header is None or all(re.fullmatch(r':?-{3,}:?', c) for c in cells):
                continue
            # Only the canonical pass table is writable; refuse ambiguous rows.
            require(len(cells) == len(self.header))
            row = dict(zip(self.header,cells));pid = row['pass_id']
            require(re.fullmatch(r'0|[1-9][0-9]*|retro-[0-9]+',pid) is not None and pid not in self.rows)
            self.rows[pid] = row;self.positions[pid] = index
        require(self.header is not None)

    def update(self, pid, fields):
        require(isinstance(fields,dict) and fields)
        require(set(fields)<=AUTHORED,'WRAPPER_OWNED_FIELD')
        fields = {key:cell(value) for key,value in fields.items()}
        before = self.rows.get(pid)
        if before is None:
            require(set(fields) == AUTHORED)
            row = {'pass_id':pid, **fields}
            position = max(self.positions.values(),default=self.header_line+1)+1
        else:
            row = {**before, **fields};position=self.positions[pid]
        # A changed draft must not carry green results from its prior revision.
        row.update({name:UNMEASURED if name in UNMEASURED_FIELDS else 'pending'
                    for name in PROTECTED & set(self.header)})
        line = '| '+' | '.join(row[name] for name in self.header)+' |\n'
        lines = list(self.lines)
        if before is None:lines.insert(position,line)
        else:lines[position]=line
        return ''.join(lines).encode(),before,row


def current_prose_lines(data, pass_id):
    """Keep current prose and original line numbers; prior pass rows are history."""
    card=Scorecard(data)
    historical={index for pid,index in card.positions.items()
                if pid.startswith('retro-') or int(pid)<int(pass_id)}
    return [(index+1,line.rstrip('\r\n')) for index,line in enumerate(card.lines)
            if index not in historical]


def deferral_rows(data):
    reader = csv.DictReader(io.StringIO(data.decode('utf-8')))
    require(tuple(reader.fieldnames or ()) == DEFERRAL_FIELDS)
    rows = list(reader)
    require(all(set(row)==set(DEFERRAL_FIELDS) and all(isinstance(v,str) for v in row.values()) for row in rows))
    return rows


def document_operations(operations):
    updates = [op for op in operations if op.get('kind') == 'scorecard_update']
    closeouts = [op for op in operations if op.get('kind') == 'closeout']
    if not updates and not closeouts:return None
    require(len(updates)==len(closeouts)==1, 'CLOSEOUT_REQUIRED')
    update,closeout=updates[0],closeouts[0]
    schema(update, ('kind','pass_id','preimage','fields'))
    schema(closeout, ('kind','pass_id','deferrals_preimage','rework_items','deferrals'))
    require(isinstance(update['pass_id'],str) and re.fullmatch(r'[1-9][0-9]*',update['pass_id']) is not None)
    require(closeout['pass_id']==update['pass_id'], 'DOCUMENT_PASS_MISMATCH')
    require(type(closeout['rework_items']) is int and closeout['rework_items']>=0)
    require(isinstance(closeout['deferrals'],list) and len(closeout['deferrals'])<=64)
    seen=set()
    for entry in closeout['deferrals']:
        schema(entry,('subject','revisit_condition','kind'))
        for key in ('subject','revisit_condition'):
            text=cell(entry[key]);require(text==entry[key] and ';' not in text and '::' not in text)
        require(entry['kind'] in ('static','runtime') and entry['subject'] not in seen)
        seen.add(entry['subject'])
    return update,closeout


def prepare(scorecard, deferrals, operations, pass_id):
    selected=document_operations(operations)
    if selected is None:return None
    update,closeout=selected
    require(update['pass_id']==pass_id,'DOCUMENT_PASS_MISMATCH')
    require(update['preimage']==sha(scorecard) and closeout['deferrals_preimage']==sha(deferrals),
            'MIXED_DOCUMENT_PREIMAGE')
    data,before,row=Scorecard(scorecard).update(pass_id,update['fields'])
    old_rows=deferral_rows(deferrals);expected=list(old_rows)
    for entry in closeout['deferrals']:
        new={'pass_id':pass_id,'corridor':row['focus'],'subject':entry['subject'],
             'kind':entry['kind'],'deferral':entry['subject'],
             'revisit_condition':entry['revisit_condition'],'status':'open'}
        existing=[r for r in old_rows if r['pass_id']==pass_id and
                  (r['subject']==entry['subject'] or r['deferral']==entry['subject'])]
        require(not existing or (len(existing)==1 and
                all(existing[0][k]==v for k,v in new.items() if k!='subject')),'DEFERRAL_ROW_CONFLICT')
        if not existing:expected.append(new)
    return {'data':data,'before':before,'draft':row,'deferrals_before':old_rows,
            'deferrals_expected':expected,'closeout':closeout}


def bundle_hashes(scripts):
    return {p.name:sha(p.read_bytes()) for p in sorted(scripts.iterdir())
            if p.is_file() and p.suffix in ('.py','.sh')}


def run_closeout(checkout, project, slug, operations, pass_id, folder, env, scripts, *, pass_plan_sha256=None):
    scorecard=checkout/project/SCORECARD;deferrals=checkout/project/DEFERRALS
    update,closeout=document_operations(operations)
    # The draft was already prepared by the service. Never accept a client-sent
    # result or a caller-supplied executable, script directory or environment.
    draft_rows=Scorecard(scorecard.read_bytes()).rows
    draft=draft_rows[pass_id]
    require(all(draft[name]==(UNMEASURED if name in UNMEASURED_FIELDS else 'pending')
                for name in PROTECTED & draft.keys()),'WRAPPER_OWNED_FIELD')
    require(sha(deferrals.read_bytes())==closeout['deferrals_preimage'],'MIXED_DOCUMENT_PREIMAGE')
    old_deferrals=deferral_rows(deferrals.read_bytes())
    plan_path=checkout/project/'docs/reverse_engineering/inventory/pass/current_pass_plan.json'
    if pass_plan_sha256 is not None:
        require(plan_path.is_file() and sha(plan_path.read_bytes())==pass_plan_sha256,'CLOSEOUT_RESULT_INVALID')
        plan=json.loads(plan_path.read_text())
        require(str(plan.get('intended_pass_id'))==pass_id and
                type(plan.get('warning_baseline_count_at_start')) is int,'CLOSEOUT_RESULT_INVALID')
    before_files={p:sha((checkout/project/p).read_bytes()) for p in (SCORECARD,DEFERRALS)}
    # The row already contains NOTES. Passing it again would enable the
    # wrapper's prose-to-deferral fallback when the explicit list is empty.
    trusted=gate_environment.closeout_environment(env,{
        'PROJECT_PASS_CLOSEOUT_REPO_ROOT':str(checkout),'FOCUS':draft['focus'],'NOTES':'',
        'REWORK_ITEMS':str(closeout['rework_items']),
        'DEFERRALS':'; '.join(' :: '.join(entry[key] for key in ('subject','revisit_condition','kind'))
                              for entry in closeout['deferrals'])})
    hashes=bundle_hashes(scripts);started=time.monotonic();log=folder/'project-pass-closeout.log'
    with log.open('wb') as stream:
        result=subprocess.run(['/bin/bash',str(scripts/'project_pass_closeout.sh'),slug,pass_id,'strict'],
                              cwd=checkout,env=trusted,stdout=stream,stderr=subprocess.STDOUT)
    gate={'target':'project-pass-closeout','exit_code':result.returncode,
          'seconds':time.monotonic()-started,'log_sha256':sha(log.read_bytes()),'environment':dict(trusted)}
    require(hashes==bundle_hashes(scripts),'CLOSEOUT_TOOLING_CHANGED')
    if result.returncode:return [gate]
    actual_rows=Scorecard(scorecard.read_bytes()).rows
    require(set(actual_rows)==set(draft_rows) and all(actual_rows[pid]==row
            for pid,row in draft_rows.items() if pid!=pass_id),'CLOSEOUT_RESULT_INVALID')
    actual=actual_rows[pass_id]
    require(actual['verify']==actual['docs_check']=='pass' and
            actual['rework_items']==str(closeout['rework_items']),'CLOSEOUT_RESULT_INVALID')
    require(actual['focus']==draft['focus'] and actual['notes']==draft['notes'],'CLOSEOUT_RESULT_INVALID')
    require(all(actual[name].strip() and actual[name] not in ('pending',UNMEASURED)
                for name in SYNCED_FIELDS & actual.keys()),'CLOSEOUT_RESULT_INVALID')
    # Only a service-pinned pass-start snapshot enables the wrapper's delta.
    # Clients still cannot seed this or any other measured column.
    for name in UNMEASURED_FIELDS & actual.keys():
        if name=='warnings_baseline_delta' and pass_plan_sha256 is not None:
            require(sha(plan_path.read_bytes())==pass_plan_sha256 and
                    re.fullmatch(r'-?[0-9]+',actual[name]) is not None,'CLOSEOUT_RESULT_INVALID')
        else:require(actual[name]==UNMEASURED,'CLOSEOUT_RESULT_INVALID')
    # Subject keys are generated by the trusted wrapper. Validate the supplied
    # prose and disposition, without duplicating its subject-key algorithm.
    actual_deferrals=deferral_rows(deferrals.read_bytes())
    require(actual_deferrals[:len(old_deferrals)]==old_deferrals,'CLOSEOUT_RESULT_INVALID')
    expected_added=[]
    for entry in closeout['deferrals']:
        row={'pass_id':pass_id,'corridor':draft['focus'],
             'kind':entry['kind'],'deferral':entry['subject'],
             'revisit_condition':entry['revisit_condition'],'status':'open'}
        if not any(all(old[k]==v for k,v in row.items()) for old in old_deferrals):expected_added.append(row)
    added=actual_deferrals[len(old_deferrals):]
    require([{k:v for k,v in row.items() if k!='subject'} for row in added]==expected_added
            and all(row['subject'] for row in added)
            and len({(r['pass_id'],r['subject']) for r in actual_deferrals})==len(actual_deferrals),
            'CLOSEOUT_RESULT_INVALID')
    commit=subprocess.check_output(['/usr/bin/git','rev-parse','HEAD'],cwd=checkout,env=trusted,text=True).strip()
    receipt={'writer':'project_pass_closeout.sh','gate':gate,'environment':dict(trusted),'wrapper_code_hashes':hashes,
             'wrapper_base_commit':commit,'wrapper_scope':('Pinned current-project tool bundle' if pass_plan_sha256 else 'Pinned fixture-base tool bundle'),
             'pass_plan_sha256':pass_plan_sha256,
             'pass_id':pass_id,'before_files':before_files,
             'after_files':{p:sha((checkout/project/p).read_bytes()) for p in (SCORECARD,DEFERRALS)},
             'draft_row':draft,'closed_row':actual,'unchanged_deferral_rows':len(old_deferrals),
             'added_deferrals':added}
    capture=folder/'capture'
    (capture/'closeout.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (capture/'closeout.log').write_bytes(log.read_bytes())
    return [gate]
