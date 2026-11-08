"""Typed extent/disposition rows and diagnostic-backed warning curation."""
import contextlib
import csv
import io
import json
import re
import tempfile
from pathlib import Path

import data_blob_dispositions_check as blobs
from . import authored_documents as documents
from .model import digest
from .producer import require

KINDS=frozenset(('extent_rows','blob_rows','warning_baseline'))
ERRORS=frozenset(('ARTIFACT_EDIT_SCHEMA','ARTIFACT_EDIT_PREIMAGE','ARTIFACT_ROW_DUPLICATE',
                 'ARTIFACT_ROW_INVALID','ARTIFACT_LAYOUT_UNSUPPORTED','RAW_RAM_REFRESH_UNSUPPORTED',
                 'RAW_RAM_JUDGMENT_CHANGED','WARNING_NOT_CURRENT','WARNING_RATIONALE_REQUIRED',
                 'WARNING_IDENTITY_CHANGED','WARNING_LAYOUT_UNSUPPORTED','WARNING_ORDER_CHANGED'))
PATHS={'extent_rows':'docs/reverse_engineering/inventory/data_extent_assertions.csv',
       'blob_rows':'docs/reverse_engineering/inventory/data_blob_dispositions.csv',
       'warning_baseline':'docs/reverse_engineering/WARNING_BASELINE.txt'}
FIELDS={'extent_rows':['label','expected_size','reason'],'blob_rows':blobs.FIELDS}
MAX_WARNING_ENTRIES=4096
MAX_WARNING_BYTES=262144
RAW_RAM_PATH='docs/reverse_engineering/inventory/raw_ram_review.csv'
RAW_RAM_PROTECTED=('addr_hex','status','proposed_symbol','notes','last_pass_reviewed')
RAW_RAM_GENERATED=('active','operand_count','distinct_owner_count','read_count',
                   'write_count','top_readers','top_writers')


def raw_ram_changes(before,after):
    """Trusted refresh may update facts, while the judgment writer stays disabled."""
    if before==after:return []
    require(before is not None and after is not None,'RAW_RAM_REFRESH_UNSUPPORTED')
    parsed=[]
    for data in (before,after):
        try:
            reader=csv.DictReader(io.StringIO(data.decode()),strict=True)
            require(reader.fieldnames==list(RAW_RAM_PROTECTED+RAW_RAM_GENERATED),'RAW_RAM_REFRESH_UNSUPPORTED')
            rows=list(reader)
        except (UnicodeError,csv.Error) as exc:raise ValueError('RAW_RAM_REFRESH_UNSUPPORTED') from exc
        require(all(set(row)==set(RAW_RAM_PROTECTED+RAW_RAM_GENERATED)
                    and all(isinstance(v,str) for v in row.values()) for row in rows),'RAW_RAM_REFRESH_UNSUPPORTED')
        require(len({r['addr_hex'] for r in rows})==len(rows),'RAW_RAM_REFRESH_UNSUPPORTED')
        parsed.append(rows)
    old,new=parsed
    require([r['addr_hex'] for r in old]==[r['addr_hex'] for r in new],'RAW_RAM_REFRESH_UNSUPPORTED')
    result=[]
    for index,(a,b) in enumerate(zip(old,new)):
        require(all(a[k]==b[k] for k in RAW_RAM_PROTECTED),'RAW_RAM_JUDGMENT_CHANGED')
        fields=[k for k in RAW_RAM_GENERATED if a[k]!=b[k]]
        if fields:result.append({'key':a['addr_hex'],'row_index':index,'changed_fields':fields,
                                'before':{k:a[k] for k in fields},'after':{k:b[k] for k in fields}})
    return result


def row_hash(row):return digest(json.dumps(row,sort_keys=True,separators=(',',':')).encode())


def operations(ops):
    selected=[op for op in ops if op.get('kind') in KINDS]
    require(len({op['kind'] for op in selected})==len(selected),'ARTIFACT_EDIT_SCHEMA')
    for op in selected:
        field='entries' if op['kind']=='warning_baseline' else 'changes'
        limit=MAX_WARNING_ENTRIES if field=='entries' else 256
        require(set(op)=={'kind','preimage','reason',field} and isinstance(op['reason'],str)
                and 0<len(op['reason'].strip())<=2000 and isinstance(op[field],list) and len(op[field])<=limit,'ARTIFACT_EDIT_SCHEMA')
        if field=='entries':
            require(len(json.dumps(op[field],ensure_ascii=False,separators=(',',':')).encode())<=MAX_WARNING_BYTES,
                    'ARTIFACT_EDIT_SCHEMA')
    return selected


def read_rows(data,kind):
    raw=[line for line in (data or b'').decode().splitlines() if line.strip() and not line.lstrip().startswith('#')]
    reader=csv.DictReader(raw)
    if not raw:return []
    require(reader.fieldnames==FIELDS[kind],'ARTIFACT_EDIT_SCHEMA')
    rows=list(reader)
    require(all(set(row)==set(FIELDS[kind]) and all(isinstance(v,str) for v in row.values()) for row in rows),'ARTIFACT_EDIT_SCHEMA')
    require(len({r['label'] for r in rows})==len(rows),'ARTIFACT_ROW_DUPLICATE')
    return rows


def csv_bytes(before,rows,kind):
    """A row edit owns its row, not other rows' quoting or surrounding prose."""
    lines=(before or b'').splitlines(keepends=True)
    content=[i for i,line in enumerate(lines) if line.strip() and not line.lstrip().startswith(b'#')]
    old=read_rows(before,kind)
    if len(content)>1:
        first,last=content[1],content[-1]
        require(content[1:]==list(range(first,last+1)),'ARTIFACT_LAYOUT_UNSUPPORTED')
        header,raw,footer=b''.join(lines[:first]),lines[first:last+1],b''.join(lines[last+1:])
    else:header,raw,footer=before or b'',[],b''
    require(len(raw)==len(old),'ARTIFACT_LAYOUT_UNSUPPORTED')
    for line,row in zip(raw,old):
        try:parsed=list(csv.reader([line.decode()],strict=True))
        except csv.Error:raise ValueError('ARTIFACT_LAYOUT_UNSUPPORTED') from None
        require(parsed==[[row[field] for field in FIELDS[kind]]],'ARTIFACT_LAYOUT_UNSUPPORTED')
    if before is not None and rows==old:return before

    def ending(line):
        return b'\r\n' if line.endswith(b'\r\n') else b'\r' if line.endswith(b'\r') else b'\n' if line.endswith(b'\n') else b''

    default=next((ending(line) for line in raw if ending(line)),ending(header) or b'\n')
    require(not header or ending(header),'ARTIFACT_LAYOUT_UNSUPPORTED')
    if not content:header+=(','.join(FIELDS[kind])).encode()+default
    previous={row['label']:(row,line) for row,line in zip(old,raw)}
    body=[]
    for index,row in enumerate(rows):
        prior,line=previous.get(row['label'],(None,b''))
        if row!=prior:
            stream=io.StringIO()
            writer=csv.writer(stream,lineterminator='\n')
            writer.writerow([row[field] for field in FIELDS[kind]])
            line=stream.getvalue()[:-1].encode()+(ending(line) if prior is not None else default)
        if (index<len(rows)-1 or footer) and not ending(line):line+=default
        body.append(line)
    return header+b''.join(body)+footer


def warning_layout(before):
    """Keep surrounding trivia opaque; row-only edits cannot own section breaks."""
    if before is None:return b'# symbol|rationale\n',[],b''
    lines=before.splitlines(keepends=True)
    trivia=[not line.strip() or line.lstrip().startswith(b'#') for line in lines]
    rows=[i for i,is_trivia in enumerate(trivia) if not is_trivia]
    if not rows:return before,[],b''
    first,last=rows[0],rows[-1]
    require(not any(trivia[first:last+1]),'WARNING_LAYOUT_UNSUPPORTED')
    return b''.join(lines[:first]),lines[first:last+1],b''.join(lines[last+1:])


def warning_bytes(before,rows,base,model):
    header,old_lines,footer=warning_layout(before)
    proposed=('\n'.join(rows)+('\n' if rows else '')).encode()
    old=entries(before,'warning_baseline');new=entries(proposed,'warning_baseline')
    if before is not None and old==new:return before
    old_order=[base.ids[base.declarations[name]] for name in old if name in base.declarations]
    new_order=[model.ids[model.declarations[name]] for name in new]
    surviving=set(old_order)&set(new_order)
    require([ident for ident in old_order if ident in surviving]==
            [ident for ident in new_order if ident in surviving],'WARNING_ORDER_CHANGED')
    require(not rows or not header or header.endswith((b'\n',b'\r')),'WARNING_LAYOUT_UNSUPPORTED')
    raw={next(iter(entries(line,'warning_baseline'))):line for line in old_lines}
    sample=old_lines[0] if old_lines else header
    ending=b'\r\n' if sample.endswith(b'\r\n') else b'\r' if sample.endswith(b'\r') else b'\n'
    body=[]
    for index,row in enumerate(rows):
        name=row.split('|',1)[0]
        line=raw[name] if name in old and old[name]==new[name] else row.encode()+ending
        if (index<len(rows)-1 or footer) and not line.endswith((b'\n',b'\r')):line+=ending
        body.append(line)
    return header+b''.join(body)+footer


def validate_blob_rows(checkout,project,path,rows,document_changes):
    """Run the unchanged row checker against the candidate's citation existence."""
    project_root=(checkout/project).resolve()
    updates={item['path']:item['after'] for item in document_changes}
    with tempfile.TemporaryDirectory(prefix='blob-citations-') as folder:
        projected=Path(folder)
        for row in rows:
            for part in blobs.artifact_paths(row['artifact']):
                file=blobs.artifact_file_part(part)
                require(not Path(file).is_absolute(),'ARTIFACT_ROW_INVALID')
                original=(project_root/'docs/reverse_engineering'/file).resolve()
                require(original.is_relative_to(project_root),'ARTIFACT_ROW_INVALID')
                relative=original.relative_to(project_root)
                key=project+relative.as_posix()
                exists=(updates[key] is not None) if key in updates else original.is_file()
                if exists:
                    target=projected/relative;target.parent.mkdir(parents=True,exist_ok=True)
                    target.touch()
        with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()):
            okay,_=blobs.validate_rows(checkout/path,projected/'docs/reverse_engineering',rows,'process')
        require(okay,'ARTIFACT_ROW_INVALID')


def prepare(checkout,manifest,ops,project,document_changes=()):
    result=[]
    for op in operations(ops):
        path=project+PATHS[op['kind']];before=documents.read(checkout,manifest,path)
        require(documents.sha(before)==op['preimage'],'ARTIFACT_EDIT_PREIMAGE')
        if op['kind']=='warning_baseline':
            header,_,_=warning_layout(before)
            require(not op['entries'] or not header or header.endswith((b'\n',b'\r')),'WARNING_LAYOUT_UNSUPPORTED')
            # The fresh diagnostic set is available only after certification.
            for row in op['entries']:
                require(isinstance(row,dict) and set(row)=={'declaration_id','rationale'}
                        and isinstance(row['declaration_id'],str),'ARTIFACT_EDIT_SCHEMA')
                reason=row['rationale']
                require(isinstance(reason,str) and 0<len(reason.strip())<=2000 and not any(c in reason for c in '|\r\n\x00')
                        and reason.strip().lower() not in ('unused','retained','intentional','baseline',
                            'unused symbol','unused symbol retained','baseline warning retained'), 'WARNING_RATIONALE_REQUIRED')
            result.append({'path':path,'before':before,'after':None,'op':op});continue
        rows=read_rows(before,op['kind']);seen=set();base_keys={row['label'] for row in rows};anchors=set()
        for change in op['changes']:
            require(isinstance(change,dict) and set(change) in ({'key','preimage','row'},{'key','preimage','row','before_key'})
                    and isinstance(change['key'],str),'ARTIFACT_EDIT_SCHEMA')
            key=change['key'];require(key not in seen,'ARTIFACT_ROW_DUPLICATE');seen.add(key)
            matches=[i for i,row in enumerate(rows) if row['label']==key]
            old=rows[matches[0]] if matches else None
            require((row_hash(old) if old else None)==change['preimage'],'ARTIFACT_EDIT_PREIMAGE')
            row=change['row']
            require(old is not None or row is not None,'ARTIFACT_EDIT_SCHEMA')
            if 'before_key' in change:
                anchor=change['before_key']
                require(old is None and row is not None and isinstance(anchor,str),'ARTIFACT_EDIT_SCHEMA')
                require(anchor in base_keys and any(r['label']==anchor for r in rows),'ARTIFACT_ROW_INVALID')
                anchors.add(anchor)
            if row is not None:
                require(isinstance(row,dict) and set(row)==set(FIELDS[op['kind']]) and row['label']==key
                        and all(isinstance(v,str) and len(v)<=2000 and not any(c in v for c in '\r\n\x00') for v in row.values()),'ARTIFACT_EDIT_SCHEMA')
                if op['kind']=='extent_rows':
                    require(re.fullmatch('[A-Za-z_][A-Za-z0-9_]*',key) is not None and row['reason'].strip()
                            and re.fullmatch('[0-9]+',row['expected_size']) is not None and int(row['expected_size'])>0,'ARTIFACT_ROW_INVALID')
            if matches:
                if row is None:rows.pop(matches[0])
                else:rows[matches[0]]=row
            elif 'before_key' in change:rows.insert(next(i for i,r in enumerate(rows) if r['label']==anchor),row)
            else:rows.append(row)
        require(anchors<={row['label'] for row in rows},'ARTIFACT_ROW_INVALID')
        require(len({r['label'] for r in rows})==len(rows),'ARTIFACT_ROW_DUPLICATE')
        if op['kind']=='blob_rows':
            validate_blob_rows(checkout,project,path,rows,document_changes)
        result.append({'path':path,'before':before,'after':csv_bytes(before,rows,op['kind']),'op':op})
    return result


def current_lines(data,kind):
    if kind=='warning_baseline':
        return [(i,line) for i,line in enumerate(data.decode().splitlines(),1) if line.strip() and not line.lstrip().startswith('#')]
    return [(i,' '.join(row.values())) for i,row in enumerate(read_rows(data,kind),2)]


def entries(data,kind):
    if kind!='warning_baseline':return {row['label']:row for row in read_rows(data,kind)}
    rows={}
    for _,line in current_lines(data or b'',kind):
        parts=line.split('|',1);require(len(parts)==2,'ARTIFACT_EDIT_SCHEMA')
        name=parts[0].strip();require(name not in rows,'ARTIFACT_ROW_DUPLICATE')
        rows[name]={'symbol':name,'rationale':parts[1].strip()}
    return rows


def changes(before,after,op):
    old=entries(before,op['kind']);new=entries(after,op['kind']);rows=[]
    old_positions={key:i for i,key in enumerate(old)};new_positions={key:i for i,key in enumerate(new)}
    for key in sorted(old.keys()|new.keys()):
        for field in sorted(old.get(key,{}).keys()|new.get(key,{}).keys()):
            left=old.get(key,{}).get(field);right=new.get(key,{}).get(field)
            if left!=right:rows.append({'key':key,'field':field,'before':left,'after':right,
                'row_index_before':old_positions.get(key),'row_index_after':new_positions.get(key)})
    return rows


def preview_rows(ops):
    result=[]
    for op in operations(ops):
        if op['kind']=='warning_baseline':
            result.extend({'kind':op['kind'],'reason':op['reason'],'row':row} for row in op['entries']);continue
        for change in op['changes']:
            result.extend({'kind':op['kind'],'reason':op['reason'],'key':change['key'],
                           'row_preimage':change['preimage'],'field':field,'after':value,
                           'insert_before_key':change.get('before_key')}
                          for field,value in (change['row'] or {'deleted':True}).items())
    return result


def preview_warning(model,op,operations):
    renames={o['declaration_id']:o['new_name'] for o in operations if o['kind']=='rename'}
    rows=[]
    for entry in op['entries']:
        ident=entry['declaration_id']
        name=ident[4:] if ident.startswith('new:') else renames.get(ident,model.name(model.node(ident)))
        rows.append(name+'|'+entry['rationale'])
    return ('\n'.join(rows)+'\n').encode()


def warning_changes(before,after,base,model):
    """Carry assembler declaration identity through rename/split transitions."""
    old=entries(before,'warning_baseline');new=entries(after,'warning_baseline')
    matched=set();result=[]
    def extent(m,node):
        from .evidence_views import data_rows
        try:
            operands=data_rows(m,m.ids[node])
        except ValueError as error:
            if str(error)!='EVIDENCE_RANGE_INVALID':raise
            return None
        if len({r['segment_id'] for r in operands})!=1:return None
        return (operands[0]['segment_id'],operands[0]['output_offset'],
                operands[-1]['output_offset']+operands[-1]['byte_length'])
    for name,row in old.items():
        node=base.declarations.get(name)
        ident=base.ids[node] if node is not None else None
        newer=model.nodes.get(ident)
        target=model.name(newer) if newer in model.declaration_records else None
        after_row=new.get(target)
        if after_row is not None:
            matched.add(target)
            kind='retain' if name==target else 'rename'
            if kind=='rename':
                a,b=extent(base,node),extent(model,newer)
                if a and b and a[:2]==b[:2] and b[2]<a[2]:kind='rename_and_split'
                else:require(row['rationale']==after_row['rationale'],'WARNING_IDENTITY_CHANGED')
        else:kind='warning_disappears_after_rename' if target and target!=name else 'remove'
        if row!=after_row:
            result.append({'transition':kind,'declaration_id':ident,'source_rename_target':target,
                           'before':row,'after':after_row})
    for name,row in new.items():
        if name not in matched:
            node=model.declarations.get(name)
            require(node is not None,'WARNING_IDENTITY_CHANGED')
            result.append({'transition':'add','declaration_id':model.ids[node],
                           'source_rename_target':name,'before':None,'after':row})
    return result


def warnings(checkout,model,ops,project,base,before):
    op=next((o for o in operations(ops) if o['kind']=='warning_baseline'),None)
    if op is None:return
    # This is the assembler's diagnostic grammar, not an assembly-source parser.
    log=(model.capture/'producer.log').read_text(errors='replace')
    actual=set(re.findall(r"warning: `([A-Za-z_][A-Za-z0-9_]*)' defined but not used",log))
    added={o['name'] for o in ops if o['kind']=='declare'}
    added.update(b['name'] for o in ops if o['kind']=='reflow_data' for b in o.get('boundaries',[]))
    records=[{'symbol':name,'declaration_id':'new:'+name if name in added else model.ids[model.declarations[name]],
              'warning':'defined but not used'} for name in sorted(actual)]
    def current(test):
        if not test:
            from .service import ServiceError
            raise ServiceError('WARNING_NOT_CURRENT',records=records,
                message='The proposed baseline must exactly match these fresh assembler warnings.')
    rows=[];seen=set()
    for entry in op['entries']:
        ident=entry['declaration_id']
        if ident.startswith('new:'):n=model.declarations.get(ident[4:])
        else:n=model.nodes.get(ident)
        current(n in model.declaration_records)
        name=model.name(n);current(name in actual and name not in seen);seen.add(name)
        rows.append(name+'|'+entry['rationale'])
    current(seen==actual)
    data=warning_bytes(before,rows,base,model)
    transitions=warning_changes(before,data,base,model)
    target=checkout/project/PATHS['warning_baseline'];target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(data)
    (model.capture/'warning-curation.json').write_text(json.dumps({'current_warnings':sorted(actual),
        'diagnostic_sha256':digest(log.encode()),'entries':op['entries'],
        'transitions':transitions},sort_keys=True)+'\n')


def extents(checkout,model,ops,project):
    import fnmatch
    for op in operations(ops):
        if op['kind']=='blob_rows':
            for change in op['changes']:
                if change['row'] is not None:
                    require(any(fnmatch.fnmatchcase(name,change['key']) for name in model.declarations),'ARTIFACT_ROW_INVALID')
    if not any(op['kind']=='extent_rows' for op in ops):return
    from .evidence_views import data_rows
    path=checkout/project/PATHS['extent_rows']
    for row in read_rows(path.read_bytes(),'extent_rows'):
        n=model.declarations.get(row['label']);require(n is not None,'ARTIFACT_ROW_INVALID')
        operands=data_rows(model,model.ids[n])
        require(len({r['segment_id'] for r in operands})==1 and
                sum(r['byte_length'] for r in operands)==int(row['expected_size']), 'ARTIFACT_ROW_INVALID')
