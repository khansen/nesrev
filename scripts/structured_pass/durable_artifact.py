"""Step 1: retain certified content and its evidence, without temporary paths.

This is an integrity/retention layer, not a new assembler or certification gate.
Only the trusted service exports already-certified generations. Blobs are private
to the service; there is no agent-facing bulk-source endpoint.
"""
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import tempfile

SCHEMAS = {'artifact':'structured-pass-artifact-v3','facts':'xasm-source-model:1:asm-edit-v1',
           'units':'xasm-source-model:1','record_ids':'stable-ids-v2'}
FACT_READERS = ('producer.py','wire_schema.py','model.py','source-model.schema.json','nes_graphics.py')
UNSPECIFIED_BASE = object()
PUBLIC_ERRORS = frozenset('''ARTIFACT_PATH_INVALID ARTIFACT_UNIT_MISMATCH
    ARTIFACT_MANIFEST_MISMATCH ARTIFACT_BLOB_MISMATCH ARTIFACT_FILE_MISMATCH
    ARTIFACT_PROVENANCE_MISMATCH ARTIFACT_CAPTURE_MISMATCH ARTIFACT_SCHEMA_UNSUPPORTED
    TOOLING_IDENTITY_MISMATCH TOOLCHAIN_UNAVAILABLE BASE_ARTIFACT_MISMATCH
    CAPTURE_CHANGED GENERATION_INPUT_CHANGED REFERENCE_CHANGED
    INSUFFICIENT_DISK_SPACE DESTINATION_EXISTS'''.split())


def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def digest(data):return hashlib.sha256(data).hexdigest()
def content_id(manifest,reference):return 'C-'+digest(canonical({'files':manifest,'reference':reference}))
def tooling_id(producer,readers):
    require(set(readers)==set(FACT_READERS),'TOOLING_IDENTITY_MISMATCH')
    return 'T-'+digest(canonical({'producer':producer,'readers':readers,
        'schemas':{k:v for k,v in SCHEMAS.items() if k!='artifact'}}))


def running_tooling(producer_path,reader_paths=None):
    # Default paths are the modules actually imported by this process, not the
    # index's recorded identity or a different package found by path convention.
    if reader_paths is None:
        from . import model
        reader_paths={name:(Path(model.producer.rom.__file__) if name=='nes_graphics.py'
                           else Path(model.__file__).with_name(name)) for name in FACT_READERS}
    require(set(reader_paths)==set(FACT_READERS),'TOOLING_IDENTITY_MISMATCH')
    return {'producer_sha256':digest(Path(producer_path).read_bytes()),
            'reader_hashes':{name:digest(Path(path).read_bytes()) for name,path in reader_paths.items()}}


def require(test,code):
    if not test:raise ValueError(code)


def safe_path(value):
    require(isinstance(value,str) and value and '\\' not in value,'ARTIFACT_PATH_INVALID')
    p=PurePosixPath(value)
    require(not p.is_absolute() and all(x not in ('.','..','') for x in value.split('/')),'ARTIFACT_PATH_INVALID')
    return value


def source_from_units(data):
    from .producer import reconstruct
    try:
        files=reconstruct(json.loads(data))
        require(len(files)==1,'ARTIFACT_UNIT_MISMATCH')
        return next(iter(files.values()))
    except (ValueError,KeyError,TypeError):raise ValueError('ARTIFACT_UNIT_MISMATCH') from None


class Store:
    def __init__(self, root):
        self.root=Path(root).resolve()
        self.root.mkdir(parents=True,exist_ok=True)

    def preflight(self,bytes_needed):
        require(shutil.disk_usage(self.root).free >= bytes_needed+256*1024**2,'INSUFFICIENT_DISK_SPACE')

    def blob_path(self,sha):
        require(isinstance(sha,str) and re.fullmatch('[0-9a-f]{64}',sha),'ARTIFACT_MANIFEST_MISMATCH')
        return self.root/'blobs'/(sha+'.gz')

    def put(self,data):
        sha=digest(data);path=self.blob_path(sha)
        if path.exists():
            require(self.get(sha)==data,'ARTIFACT_BLOB_MISMATCH');return sha
        self.preflight(len(data));path.parent.mkdir(parents=True,exist_ok=True)
        fd,tmp=tempfile.mkstemp(prefix='.pending-',dir=path.parent)
        try:
            with os.fdopen(fd,'wb') as stream:
                stream.write(gzip.compress(data,mtime=0));stream.flush();os.fsync(stream.fileno())
            os.replace(tmp,path)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)
        return sha

    def get(self,sha,code='ARTIFACT_BLOB_MISMATCH'):
        try:data=gzip.decompress(self.blob_path(sha).read_bytes())
        except (OSError,EOFError,ValueError):raise ValueError(code) from None
        require(digest(data)==sha,code)
        return data

    def export(self,state,generation,source_path,reference_path,reader_roots,
               producer_path,producer_recipe,base_artifact=None,*,review_pass_id=None):
        record=state['generations'][generation];manifest=record['manifest']
        source_path=safe_path(source_path);reference_path=safe_path(reference_path)
        require(source_path in manifest,'ARTIFACT_MANIFEST_MISMATCH')
        capture=Path(record['capture']);checkout=Path(record['checkout'])
        expected=record['capture_hashes']
        require(set(expected)=={f.name for f in capture.iterdir() if f.is_file()},'CAPTURE_CHANGED')
        self.preflight(sum(f.stat().st_size for f in capture.iterdir() if f.is_file()))
        captures={}
        for name,sha in expected.items():
            safe_path(name);data=(capture/name).read_bytes()
            require(digest(data)==sha,'CAPTURE_CHANGED');captures[name]=self.put(data)
        units=self.get(captures['model.json'],'ARTIFACT_UNIT_MISMATCH')
        source=source_from_units(units)
        require(digest(source)==manifest[source_path],'ARTIFACT_UNIT_MISMATCH')
        files={}
        for relative,sha in manifest.items():
            safe_path(relative)
            # The original asm is deliberately never opened.
            data=source if relative==source_path else (checkout/relative).read_bytes()
            require(digest(data)==sha,'GENERATION_INPUT_CHANGED')
            files[relative]={'sha256':sha,'mode':0o644 if relative==source_path else (checkout/relative).stat().st_mode & 0o777,
                             'storage':'units' if relative==source_path else 'blob'}
            if relative!=source_path:self.put(data)
        reference=(checkout/reference_path).read_bytes()
        require(digest(reference)==state['reference_sha256'],'REFERENCE_CHANGED')
        self.put(reference)
        readers={**state['reader_hashes'],'durable_artifact.py':digest(Path(__file__).read_bytes())}
        reader_blobs={}
        reader_paths={}
        for relative,sha in readers.items():
            safe_path(relative)
            choices=[Path(root)/relative for root in reader_roots]
            if relative=='durable_artifact.py':choices.append(Path(__file__))
            found=next((f for f in choices if f.is_file() and digest(f.read_bytes())==sha),None)
            require(found is not None,'TOOLCHAIN_UNAVAILABLE')
            reader_blobs[relative]=self.put(found.read_bytes())
            reader_paths[relative]=found
        binary=Path(producer_path).read_bytes()
        require(digest(binary)==state['producer_sha256'],'TOOLCHAIN_UNAVAILABLE')
        producer_blob=self.put(binary)
        recipe_path=Path(producer_recipe);recipe_data=recipe_path.read_bytes()
        recipe_blob=self.put(recipe_data);recipe=json.loads(recipe_data)
        toolchain_files={}
        for name,key in [('source.tar.gz','source_archive_sha256'),('local.patch','local_diff_sha256')]:
            data=(recipe_path.parent/name).read_bytes()
            require(digest(data)==recipe[key],'TOOLCHAIN_UNAVAILABLE')
            toolchain_files[name]=self.put(data)
        fact_readers={name:readers[name] for name in FACT_READERS}
        tid=tooling_id(state['producer_sha256'],fact_readers)
        certified_inputs=running_tooling(producer_path,{name:reader_paths[name] for name in FACT_READERS})
        cid=content_id(manifest,state['reference_sha256'])
        if record['base'] is None:require(base_artifact is None,'BASE_ARTIFACT_MISMATCH')
        else:
            require(base_artifact is not None,'BASE_ARTIFACT_MISMATCH')
            base=self.open(base_artifact,certified_inputs)
            old=state['generations'][record['base']]
            require(base['content_id']==content_id(old['manifest'],state['reference_sha256']),
                    'BASE_ARTIFACT_MISMATCH')
            require(base['legacy_generation']==record['base'],'BASE_ARTIFACT_MISMATCH')
        provenance_blob=self.put(canonical(record.get('provenance',[])))
        body={'schema':SCHEMAS['artifact'],'schemas':SCHEMAS,'content_id':cid,'tooling_id':tid,
              'legacy_generation':generation,'manifest':manifest,'files':files,
              'source_path':source_path,'reference_path':reference_path,
              'reference_sha256':state['reference_sha256'],'captures':captures,
              'provenance':provenance_blob,'base_artifact':base_artifact,
              'producer_sha256':producer_blob,'reader_hashes':fact_readers,
              'support_code_hashes':{name:sha for name,sha in reader_blobs.items() if name not in FACT_READERS},
              'producer_recipe':recipe_blob,'toolchain_files':toolchain_files,
              'commit_scope':'Carried project bytes are authoritative; no claim that a candidate was committed.'}
        if record.get('review_anchor') is not None:
            body['review_anchor']=record['review_anchor']
        if review_pass_id is not None:
            require(isinstance(review_pass_id,str) and review_pass_id.isdigit(),'ARTIFACT_MANIFEST_MISMATCH')
            body['review_pass_id']=review_pass_id
        eid='E-'+digest(canonical(body));out=self.root/'artifacts'/eid/'receipt.json'
        out.parent.mkdir(parents=True,exist_ok=True)
        if out.exists():require(out.read_bytes()==canonical(body),'ARTIFACT_MANIFEST_MISMATCH')
        else:
            fd,temporary=tempfile.mkstemp(prefix='.pending-',dir=out.parent)
            try:
                with os.fdopen(fd,'wb') as stream:
                    stream.write(canonical(body));stream.flush();os.fsync(stream.fileno())
                os.replace(temporary,out)
            finally:
                if os.path.exists(temporary):os.unlink(temporary)
        self.open(eid,certified_inputs,base_artifact)
        return {'artifact_id':eid,'content_id':cid,'tooling_id':tid,'receipt':str(out)}

    def open(self,eid,runtime,expected_base=UNSPECIFIED_BASE):
        require(isinstance(eid,str) and re.fullmatch('E-[0-9a-f]{64}',eid),'ARTIFACT_MANIFEST_MISMATCH')
        try:body=json.loads((self.root/'artifacts'/eid/'receipt.json').read_bytes())
        except (OSError,ValueError):raise ValueError('ARTIFACT_MANIFEST_MISMATCH') from None
        require('E-'+digest(canonical(body))==eid,'ARTIFACT_MANIFEST_MISMATCH')
        require(body['schema']==SCHEMAS['artifact'] and body['schemas']==SCHEMAS,'ARTIFACT_SCHEMA_UNSUPPORTED')
        require(body['tooling_id']==tooling_id(body['producer_sha256'],body['reader_hashes']),
                'ARTIFACT_MANIFEST_MISMATCH')
        require(body['tooling_id']==tooling_id(runtime['producer_sha256'],runtime['reader_hashes']),
                'TOOLING_IDENTITY_MISMATCH')
        if expected_base is not UNSPECIFIED_BASE:require(body['base_artifact']==expected_base,'BASE_ARTIFACT_MISMATCH')
        require(body['content_id']==content_id(body['manifest'],body['reference_sha256']),
                'ARTIFACT_MANIFEST_MISMATCH')
        require(set(body['files'])==set(body['manifest']),'ARTIFACT_MANIFEST_MISMATCH')
        source=source_from_units(self.get(body['captures']['model.json'],'ARTIFACT_UNIT_MISMATCH'))
        for name,entry in body['files'].items():
            safe_path(name)
            require(entry['sha256']==body['manifest'][name],'ARTIFACT_MANIFEST_MISMATCH')
            if name==body['source_path']:
                require(entry['storage']=='units' and digest(source)==entry['sha256'],'ARTIFACT_UNIT_MISMATCH')
            else:
                require(entry['storage']=='blob','ARTIFACT_MANIFEST_MISMATCH')
                self.get(entry['sha256'],'ARTIFACT_FILE_MISMATCH')
        self.get(body['provenance'],'ARTIFACT_PROVENANCE_MISMATCH')
        for name,sha in body['captures'].items():safe_path(name);self.get(sha,'ARTIFACT_CAPTURE_MISMATCH')
        self.get(body['reference_sha256'],'REFERENCE_CHANGED')
        self.get(body['producer_sha256'],'TOOLCHAIN_UNAVAILABLE')
        self.get(body['producer_recipe'],'TOOLCHAIN_UNAVAILABLE')
        for sha in body['toolchain_files'].values():self.get(sha,'TOOLCHAIN_UNAVAILABLE')
        for relative,sha in body['reader_hashes'].items():safe_path(relative);self.get(sha,'TOOLCHAIN_UNAVAILABLE')
        for relative,sha in body['support_code_hashes'].items():safe_path(relative);self.get(sha,'TOOLCHAIN_UNAVAILABLE')
        return body

    def materialize(self,eid,runtime,destination,expected_base=UNSPECIFIED_BASE):
        body=self.open(eid,runtime,expected_base);destination=Path(destination)
        require(not destination.exists(),'DESTINATION_EXISTS')
        self.preflight(sum(len(self.get(sha)) for sha in body['captures'].values()))
        destination.mkdir(parents=True)
        source=source_from_units(self.get(body['captures']['model.json']))
        for name,entry in body['files'].items():
            target=destination/'project'/name;target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(source if name==body['source_path'] else self.get(entry['sha256']))
            target.chmod(entry['mode'])
        ref=destination/'project'/safe_path(body['reference_path']);ref.parent.mkdir(parents=True,exist_ok=True)
        ref.write_bytes(self.get(body['reference_sha256']))
        for name,sha in body['captures'].items():
            target=destination/'capture'/safe_path(name);target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(self.get(sha))
        return body
