"""Bounded gate explanations, with source snippets replaced by producer records."""
import json
from pathlib import Path
import re
from .review_pages import wire_size

TAIL_BYTES=256*1024
MAX_LINES=40
MAX_CONTEXT_LINES=120
MAX_ITEMS=80
MAX_STRING=2048
MAX_OUTPUT=12288


def explanation(path,checkout,source,model,*,max_output=MAX_OUTPUT):
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
    # Bare symbol names and punctuation are useful diagnostic vocabulary,
    # not source excerpts. Match substantive snippets against the original text.
    snippets=sorted((s for s in source_lines if any(c.isalnum() for c in s)
                     and not re.fullmatch(r'[A-Za-z_@][A-Za-z0-9_@]*',s)),key=len,reverse=True)

    def clean_string(value):
        nonlocal truncated
        # Apply snippet redaction to every channel, including prefixed plain
        # lines and scalar JSON fields, before removing filesystem prefixes.
        matches=[]
        for snippet in snippets:
            if snippet in value:
                matches.extend((m.start(),m.end()) for m in re.finditer(
                    r'(?<![A-Za-z0-9_@])'+re.escape(snippet)+r'(?![A-Za-z0-9_@])',value))
        spans=[]
        for start,end in sorted(matches):
            if spans and start<=spans[-1][1]:spans[-1]=(spans[-1][0],max(end,spans[-1][1]))
            else:spans.append((start,end))
        parts=[];end=0
        for start,stop in spans:
            parts.extend((value[end:start],'[source text omitted; use structured records]'));end=stop
        value=''.join(parts)+value[end:]
        for root in roots:value=value.replace(root+'/', '')
        # Keep project-relative paths and remove other host filesystem paths.
        value=re.sub(r'(?<![\w:/])/(?:[^\s\"\'<>:,;]+/)*[^\s\"\'<>:,;]*','[host-path]',value)
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
    # Closeout can finish with a successful subcheck's JSON after an earlier
    # failure. Keep the failure lines independently of that trailing report.
    log_lines=text.splitlines()
    failures=[i for i,line in enumerate(log_lines) if re.search(r'\b(?:FAIL|ERROR|FATAL):',line,re.I)]
    result['failure_lines']=[];result['failure_context']=[]
    def failure_text(line):
        return clean_string(line)
    for index,i in enumerate(failures[:MAX_LINES]):
        result['failure_lines'].append(failure_text(log_lines[i]))
        context=[];context_truncated=False
        for j in range(i+1,len(log_lines)):
            line=log_lines[j]
            if not line.strip() or line.lstrip().startswith(('{','[')) or j in failures:break
            if len(context)==MAX_CONTEXT_LINES:
                context_truncated=True;break
            rendered=failure_text(line);context.append(rendered)
            context_truncated |= len(rendered)>MAX_STRING
        truncated |= context_truncated
        if context:result['failure_context'].append({'failure_index':index,'lines':context,
                                                     'context_truncated':context_truncated})
    result['failure_line_count_in_tail']=len(failures)
    result['failure_lines_truncated']=len(failures)>MAX_LINES
    result['log_tail_truncated']=size>TAIL_BYTES
    truncated |= result['failure_lines_truncated']
    result['origin']='gate diagnostic, not an additional source view'
    if wire_size(result)>max_output:
        # Preserve a valid, explicitly partial JSON response, never a cut JSON string.
        truncated=True
        if report is not None:
            result['report']=clean({k:v for k,v in report.items() if not isinstance(v,(dict,list))})
            result['detail_notice']='Detailed report exceeds response budget; use the named symbols/files through navigation.'
        else:result['lines']=result['lines'][-10:]
    while wire_size(result)+32>max_output:
        if result.get('report'):result['report'].pop(next(reversed(result['report'])))
        elif result.get('lines'):result['lines'].pop(0)
        elif any(entry['lines'] for entry in result['failure_context']):
            entry=next(entry for entry in reversed(result['failure_context']) if entry['lines'])
            entry['lines'].pop();entry['context_truncated']=True
        elif len(result['failure_lines'])>1:
            index=len(result['failure_lines'])-1
            result['failure_lines'].pop();result['failure_lines_truncated']=True
            # Keep empty, flagged context entries for every visible failure.
            result['failure_context']=[entry for entry in result['failure_context'] if entry['failure_index']!=index]
        elif result['failure_lines'] and len(result['failure_lines'][0])>80:
            result['failure_lines'][0]=result['failure_lines'][0][:len(result['failure_lines'][0])//2]+'…'
            result['failure_lines_truncated']=True
        else:break
        truncated=True
    return {**result,'truncated':truncated}
