"""Operator-pinned analogue models; candidates are evidence, never naming authority."""
import json
import gzip
from pathlib import Path

from . import producer
from .model import Model


def capture(paths,destination):
    producer.require(isinstance(paths,list) and len(paths)<=2,'EVIDENCE_REQUEST_INVALID')
    entries=[]
    for index,path in enumerate(paths):
        producer.require(isinstance(path,str) and Path(path).is_absolute(),'EVIDENCE_REQUEST_INVALID')
        # Validate the copied bytes, so acquisition and the retained hash refer
        # to exactly the same input even if an operator path changes later.
        name=f'analogue-{index}.json.gz';target=destination/name
        data=Path(path).read_bytes();model,_=producer.loads(data)
        target.write_bytes(gzip.compress(data,mtime=0))
        producer.require(model['identity']['producer_sha256']==producer.sha(producer.EXE),'SOURCE_MODEL_PRODUCER')
        entries.append({'file':name,'sha256':producer.sha(target),'model_sha256':producer.digest(data),
                        'model_id':model['identity']['model_id']})
    (destination/'analogues.json').write_text(json.dumps(entries,sort_keys=True)+'\n')


def rows(model,record_id):
    n=model.node(record_id);name=model.name(n)
    producer.require(n in model.declaration_records,'EVIDENCE_REQUEST_INVALID')
    path=model.capture/'analogues.json'
    entries=json.loads(path.read_text()) if path.exists() else []
    producer.require(bool(entries),'EVIDENCE_UNAVAILABLE')
    result=[]
    for entry in entries:
        path=model.capture/entry['file']
        producer.require(producer.sha(path)==entry['sha256'],'CAPTURE_CHANGED')
        # The service has already rechecked every capture hash before this view.
        analogue=project(model,entries.index(entry));other=analogue.document
        values={e['expression_id']:e['value'] for e in other['evaluations']}
        for declaration in other['declarations']:
            value=values.get(declaration.get('expression_id'))
            same_name=declaration['name']==name
            same_value=(name in model.values and value is not None and value.get('kind')=='integer'
                        and value.get('value')==model.values[name])
            if not (same_name or same_value):continue
            result.append({'selected_record_id':record_id,'analogue_model_id':entry['model_id'],
                'analogue_index':entries.index(entry),
                'analogue_record_id':analogue.ids[declaration['syntax_id']],
                'analogue_capture_sha256':entry['sha256'],'declaration':declaration,
                'same_spelling':same_name,'same_value':same_value,
                'meaning':'unproven; inspect this analogue and the current producer/consumer contract before adopting vocabulary'})
    return result


def project(model,index):
    path=model.capture/'analogues.json'
    entries=json.loads(path.read_text()) if path.exists() else []
    producer.require(type(index) is int and 0<=index<len(entries),'EVIDENCE_REQUEST_INVALID')
    entry=entries[index];path=model.capture/entry['file']
    producer.require(producer.sha(path)==entry['sha256'],'CAPTURE_CHANGED')
    cache=getattr(model,'_analogue_models',{})
    if entry['sha256'] not in cache:cache[entry['sha256']]=Model(model.capture,analogue_file=entry['file'])
    model._analogue_models=cache
    return cache[entry['sha256']]
