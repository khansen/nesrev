"""Generation-bound Markdown operations; no source, executable or mixed-file writes."""
from pathlib import Path, PurePosixPath
import re
import hashlib

KINDS=frozenset(('document_write','document_delete'))
ERRORS=frozenset('''DOCUMENT_PATH_FORBIDDEN DOCUMENT_PREIMAGE_MISMATCH
    DOCUMENT_SCHEMA DOCUMENT_NOT_FOUND DOCUMENT_DUPLICATE_OPERATION
    DOCUMENT_DELETE_CANONICAL_FORBIDDEN DOCUMENT_PATH_CASE_MISMATCH'''.split())
CANONICAL=frozenset(name.casefold() for name in ('docs/crosswalk/TERMINOLOGY_CROSSWALK.md',
    'docs/reverse_engineering/ONBOARDING.md','docs/reverse_engineering/QUICK_REFERENCE.md',
    'docs/reverse_engineering/MEMORY_MAP.md','docs/reverse_engineering/SEMANTIC_CLAIMS.md'))


def require(ok,code):
    if not ok:raise ValueError(code)


def sha(data):return hashlib.sha256(data).hexdigest() if data is not None else None


def path_allowed(path,project,source,ownership):
    require(isinstance(path,str) and path.startswith(project) and
        all(part not in ('','.','..') and not part.startswith('.') for part in path.split('/')) and
        not any(c in path for c in '\\\x00\r\n'), 'DOCUMENT_PATH_FORBIDDEN')
    kind=ownership(path,project,source)
    if kind=='mixed':raise ValueError('MIXED_FILE_REQUIRES_TYPED_UPDATE')
    if kind=='generated':raise ValueError('GENERATED_PATH_SERVICE_OWNED')
    relative=path[len(project):].casefold()
    require(kind=='authored' and relative.startswith('docs/') and relative.endswith('.md')
            and '/inventory/' not in relative, 'DOCUMENT_PATH_FORBIDDEN')


def selected(operations,project,source,ownership):
    found=[];seen=set();spellings={}
    for op in operations:
        if op.get('kind') not in KINDS:continue
        keys={'kind','path','preimage','reason'}|({'text'} if op['kind']=='document_write' else set())
        require(set(op)==keys,'DOCUMENT_SCHEMA')
        path_allowed(op['path'],project,source,ownership)
        folded=op['path'].casefold()
        require(folded not in seen,'DOCUMENT_DUPLICATE_OPERATION');seen.add(folded)
        parts=PurePosixPath(op['path']).parts
        for end in range(1,len(parts)+1):
            prefix='/'.join(parts[:end]);key=prefix.casefold()
            require(spellings.setdefault(key,prefix)==prefix,'DOCUMENT_PATH_CASE_MISMATCH')
        require(isinstance(op['reason'],str) and bool(op['reason'].strip()) and len(op['reason'])<=2000,'DOCUMENT_SCHEMA')
        require(op['preimage'] is None or isinstance(op['preimage'],str) and re.fullmatch('[0-9a-f]{64}',op['preimage']), 'DOCUMENT_SCHEMA')
        if op['kind']=='document_write':
            require(isinstance(op['text'],str) and '\x00' not in op['text'] and len(op['text'].encode())<=262144,'DOCUMENT_SCHEMA')
        else:
            relative=op['path'][len(project):].casefold()
            require(relative not in CANONICAL and not PurePosixPath(relative).name.endswith('_dx_systems.md'),
                    'DOCUMENT_DELETE_CANONICAL_FORBIDDEN')
            require(op['preimage'] is not None,'DOCUMENT_PREIMAGE_MISMATCH')
        found.append(op)
    return found


def check_spelling(checkout,path):
    # Enumerating actual names also catches case variants on case-sensitive hosts.
    parent=Path(checkout)
    for part in PurePosixPath(path).parts:
        if not parent.exists():break
        require(parent.is_dir(),'DOCUMENT_PATH_FORBIDDEN')
        matches=[entry.name for entry in parent.iterdir() if entry.name.casefold()==part.casefold()]
        require(not matches or matches==[part],'DOCUMENT_PATH_CASE_MISMATCH')
        parent=parent/part


def read(checkout,manifest,path):
    target=Path(checkout)/path
    require(target.resolve()==target.absolute() and not target.is_symlink(),'DOCUMENT_PATH_FORBIDDEN')
    check_spelling(checkout,path)
    expected=manifest.get(path)
    if expected is None:
        require(not target.exists(),'DOCUMENT_PATH_FORBIDDEN')
        return None
    require(target.is_file(),'DOCUMENT_NOT_FOUND')
    data=target.read_bytes();require(sha(data)==expected,'DOCUMENT_PREIMAGE_MISMATCH')
    data.decode('utf-8')
    return data


def prepare(checkout,manifest,operations,project,source,ownership):
    result=[]
    for op in selected(operations,project,source,ownership):
        before=read(checkout,manifest,op['path'])
        require(sha(before)==op['preimage'],'DOCUMENT_PREIMAGE_MISMATCH')
        after=op.get('text').encode() if op['kind']=='document_write' else None
        result.append({'path':op['path'],'before':before,'after':after,'reason':op['reason']})
    return result


def describe(item):
    before=item['before'].decode().splitlines() if item['before'] is not None else []
    after=item['after'].decode().splitlines() if item['after'] is not None else []
    start=0
    while start<min(len(before),len(after)) and before[start]==after[start]:start+=1
    end=0
    while end<min(len(before),len(after))-start and before[-end-1]==after[-end-1]:end+=1
    def view(data):
        if data is None:return None
        lines=data.decode().splitlines()
        changed=lines[start:len(lines)-end]
        return {'sha256':sha(data),'line_count':len(lines),'first_changed_line':start+1,
                'changed_line_count':len(changed),'lines':changed,'truncated':False}
    return {'kind':'authored_document','path':item['path'],'reason':item['reason'],
            'before':view(item['before']),'after':view(item['after']),
            'complete_view':'document operation with generation, path, offset and limit'}
