"""Bounded gate explanations, with source snippets replaced by producer records."""
import json
from pathlib import Path
import re

TAIL_BYTES=256*1024
MAX_LINES=40
MAX_ITEMS=80
MAX_STRING=2048
MAX_OUTPUT=32768


def explanation(path,checkout,source,model):
    path=Path(path)
    with path.open('rb') as stream:
        stream.seek(0,2);size=stream.tell();stream.seek(max(0,size-TAIL_BYTES))
        text=stream.read().decode('utf-8','replace')
    truncated=size>TAIL_BYTES
    decoder=json.JSONDecoder();report=None
    # Wrapper reports are top-level objects at column zero. Inner residue
    # objects must not replace the enclosing summary when scanning backwards.
    for match in reversed(list(re.finditer(r'(?m)^\{',text))):
        try:value,_=decoder.raw_decode(text[match.start():])
        except ValueError:continue
        if isinstance(value,dict):report=value;break
    roots=sorted({str(Path(checkout)),str(Path(checkout).resolve())},key=len,reverse=True)
    source_lines={s.strip() for s in model.source.decode('utf-8','replace').splitlines() if s.strip()}

    def clean_string(value):
        nonlocal truncated
        for root in roots:value=value.replace(root+'/', '')
        # Keep project-relative paths and remove other host filesystem paths.
        value=re.sub(r'(?<![\w:/])/(?:[^\s\"\'<>:,;]+/)*[^\s\"\'<>:,;]*','[host-path]',value)
        if value.strip() in source_lines:value='[source text omitted; use structured records]'
        if len(value)>MAX_STRING:truncated=True;value=value[:MAX_STRING]+'…'
        return value

    def clean(value,depth=0):
        nonlocal truncated
        if depth>12:truncated=True;return '[depth limit]'
        if isinstance(value,str):return clean_string(value)
        if isinstance(value,list):
            truncated |= len(value)>MAX_ITEMS
            return [clean(v,depth+1) for v in value[:MAX_ITEMS]]
        if isinstance(value,dict):
            truncated |= len(value)>MAX_ITEMS
            result={clean_string(str(k)):clean(v,depth+1) for k,v in list(value.items())[:MAX_ITEMS]}
            filename=value.get('file',value.get('path',''))
            if isinstance(filename,str) and filename.casefold().endswith('.asm'):
                for key in ('text','source','source_text','excerpt','line_text'):
                    if key in result:result[key]='[source text omitted; see source_records]'
                line=value.get('line')
                if type(line) is int and (filename==source or filename.endswith('/'+source)):
                    nodes=[n for n,f in model.facts.items() if f['kind'] in ('INSTRUCTION_NODE','DATA_NODE','EQU_NODE','LABEL_NODE','LOCAL_LABEL_NODE')
                           and f['span'][0]<=line<=f['span'][2]]
                    result['source_records']=[model.statement(n) for n in nodes[:4]]
            return result
        return value

    if report is not None:
        result={'format':'json','report':clean(report)}
    else:
        lines=text.splitlines();truncated |= len(lines)>MAX_LINES
        result={'format':'text','lines':[clean_string(line) for line in lines[-MAX_LINES:]]}
    if len(json.dumps(result).encode())>MAX_OUTPUT:
        # Preserve a valid, explicitly partial JSON response, never a cut JSON string.
        truncated=True
        if report is not None:
            result={'format':'json','report':{k:clean(v) for k,v in report.items() if not isinstance(v,(dict,list))},
                    'detail_notice':'Detailed report exceeds response budget; ask for the named symbols/files through navigation.'}
        else:result['lines']=result['lines'][-10:]
    while len(json.dumps(result).encode())>MAX_OUTPUT and result.get('report'):
        result['report'].pop(next(reversed(result['report'])))
        truncated=True
    return {**result,'truncated':truncated,'origin':'gate diagnostic, not an additional source view'}
