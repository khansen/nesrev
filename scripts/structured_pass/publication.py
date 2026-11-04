"""Automatic durable export, called under the editing service's write lock.

Configuration comes from trusted session initialization, never client arguments.
The state-file commit is the publication point; immutable artifacts may precede
it so interrupted publication is retryable without losing a validated revision.
"""
import json
import os
from pathlib import Path
import re
import tempfile

from .durable_artifact import Store, canonical, digest, require, running_tooling, PUBLIC_ERRORS, UNSPECIFIED_BASE
from . import service as common
common.PUBLIC_ERROR_CODES |= PUBLIC_ERRORS

HERE=Path(__file__).resolve().parent
MAX_REVIEW_STATES=8


def persistent_root(root):
    root=Path(root).resolve()
    temporary=[Path('/private/tmp'),Path('/tmp').resolve(),Path(tempfile.gettempdir()).resolve()]
    require(not any(root.is_relative_to(p) for p in temporary),'RETENTION_PATH_INVALID')
    return root


def configuration(producer_sha256,root=None):
    require(root is not None,'RETENTION_NOT_CONFIGURED')
    root=persistent_root(root)
    toolchain=root/'toolchains'/producer_sha256
    require((toolchain/'xasm').is_file() and digest((toolchain/'xasm').read_bytes())==producer_sha256,'TOOLCHAIN_UNAVAILABLE')
    require((toolchain/'REBUILD-v2.json').is_file(),'TOOLCHAIN_UNAVAILABLE')
    return {'schema':'publication-retention-v1','root':str(root),'toolchain':str(toolchain)}


def immutable_file(path,data,mode=0o644):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():
        require(path.read_bytes()==data,'PUBLICATION_RECEIPT_MISMATCH')
        return
    fd,temporary=tempfile.mkstemp(prefix='.pending-',dir=path.parent)
    try:
        with os.fdopen(fd,'wb') as stream:
            stream.write(data);stream.flush();os.fsync(stream.fileno())
        os.chmod(temporary,mode)
        os.replace(temporary,path)
    finally:
        if os.path.exists(temporary):os.unlink(temporary)


def toolchain(store,config,sha):
    source=Path(config['toolchain']);destination=store.root/'toolchains'/sha
    binary=(source/'xasm').read_bytes()
    require(digest(binary)==sha,'TOOLCHAIN_UNAVAILABLE')
    recipe=(source/'REBUILD-v2.json').read_bytes();metadata=json.loads(recipe)
    require(metadata['producer_sha256']==sha,'TOOLCHAIN_UNAVAILABLE')
    inputs={'xasm':binary,'REBUILD-v2.json':recipe}
    for filename,key in [('source.tar.gz','source_archive_sha256'),('local.patch','local_diff_sha256')]:
        data=(source/filename).read_bytes()
        require(digest(data)==metadata[key],'TOOLCHAIN_UNAVAILABLE');inputs[filename]=data
    for filename,data in inputs.items():
        immutable_file(destination/filename,data,0o755 if filename=='xasm' else 0o644)
    return destination/'xasm',destination/'REBUILD-v2.json'


def ticket_path(store,artifact):
    require(isinstance(artifact,str) and re.fullmatch('E-[0-9a-f]{64}',artifact),'PUBLICATION_RECEIPT_MISMATCH')
    return Path(store)/'reviews'/(artifact+'.json')


def read_ticket(store,artifact):
    try:ticket=json.loads(ticket_path(store,artifact).read_bytes())
    except (OSError,ValueError):raise ValueError('PUBLICATION_RECEIPT_MISMATCH') from None
    require(isinstance(ticket,dict),'PUBLICATION_RECEIPT_MISMATCH')
    anchored=ticket.get('schema')=='published-review-v2'
    fields={'schema','artifacts','profile','producer_sha256'}|({'anchor_artifact'} if anchored else set())
    require(set(ticket)==fields,'PUBLICATION_RECEIPT_MISMATCH')
    require(ticket['schema'] in ('published-review-v1','published-review-v2') and isinstance(ticket['artifacts'],list)
            and ticket['artifacts'] and ticket['artifacts'][-1]==artifact,'PUBLICATION_RECEIPT_MISMATCH')
    # Bind the chosen window to immutable evidence, rather than trusting an
    # editable ticket to silently omit earlier states.
    try:body=json.loads((Path(store)/'artifacts'/artifact/'receipt.json').read_bytes())
    except (OSError,ValueError):raise ValueError('PUBLICATION_RECEIPT_MISMATCH') from None
    require('E-'+digest(canonical(body))==artifact and body['producer_sha256']==ticket['producer_sha256'],
            'PUBLICATION_RECEIPT_MISMATCH')
    require(body.get('review_anchor')==ticket.get('anchor_artifact'),'PUBLICATION_RECEIPT_MISMATCH')
    if anchored:require(ticket['anchor_artifact']==ticket['artifacts'][0],'PUBLICATION_RECEIPT_MISMATCH')
    return ticket


def export_chain(state,generation,source,reference,profile,*,review_pass_id=None):
    config=state.get('retention')
    require(isinstance(config,dict) and config.get('schema')=='publication-retention-v1','RETENTION_NOT_CONFIGURED')
    require(profile in ('rename','instruction'),'PUBLICATION_RECEIPT_MISMATCH')
    require(review_pass_id is None or isinstance(review_pass_id,str) and review_pass_id.isdigit(),
            'PUBLICATION_RECEIPT_MISMATCH')
    store=Store(persistent_root(config['root']))
    executable,recipe=toolchain(store,config,state['producer_sha256'])
    runtime=running_tooling(executable)
    anchor=state.get('chain_anchor')
    chain=[];seen=set();cursor=generation
    while cursor is not None:
        require(cursor not in seen and cursor in state['generations'],'BASE_ARTIFACT_MISMATCH')
        seen.add(cursor);chain.append(cursor)
        if anchor and cursor==anchor['generation']:break
        cursor=state['generations'][cursor]['base']
    chain.reverse();items=[];base=UNSPECIFIED_BASE if anchor else None
    if anchor:
        require(chain[0]==anchor['generation'] and
                state['generations'][chain[0]].get('artifact',{}).get('artifact_id')==anchor['artifact_id'],
                'BASE_ARTIFACT_MISMATCH')
        state['generations'][generation]['review_anchor']=anchor['artifact_id']
    require(2<=len(chain)<=MAX_REVIEW_STATES,'PUBLICATION_CHAIN_LIMIT')
    for gen in chain:
        record=state['generations'][gen]
        saved=record.get('artifact')
        if saved:
            body=store.open(saved['artifact_id'],runtime,base)
            require(body['legacy_generation']==gen and body['manifest']==record['manifest']
                    and body.get('review_pass_id')==review_pass_id,
                    'PUBLICATION_RECEIPT_MISMATCH')
            item=saved
        else:
            item=store.export(state,gen,source,reference,[HERE,HERE.parent],executable,recipe,base,
                              review_pass_id=review_pass_id)
            # A portable receipt is enough; do not expose server filesystem paths.
            item={k:v for k,v in item.items() if k!='receipt'}
            record['artifact']=item
        items.append(item);base=item['artifact_id']
    ticket={'schema':'published-review-v2' if anchor else 'published-review-v1',
            'artifacts':[i['artifact_id'] for i in items],
            'profile':profile,'producer_sha256':state['producer_sha256']}
    if anchor:ticket['anchor_artifact']=anchor['artifact_id']
    immutable_file(ticket_path(store.root,base),canonical(ticket))
    return {**items[-1],'base_artifact':items[-2]['artifact_id'],
            'artifact_chain':ticket['artifacts'],'profile':profile}
