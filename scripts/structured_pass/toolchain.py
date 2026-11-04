"""Operator-only build from the checksum-pinned official XORcyst release."""
import io
import json
import argparse
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

from .producer import digest, require
from .publication import immutable_file, persistent_root

PIN = Path(__file__).resolve().parents[2]/'docs/structured-pass/producer.json'


def build(archive_path, store_root):
    archive=Path(archive_path).read_bytes()
    pin=json.loads(PIN.read_text());commit=pin['commit']
    require(digest(archive)==pin['archive_sha256'],'PRODUCER_ARCHIVE_CHANGED')
    root=persistent_root(store_root)
    root.mkdir(parents=True,exist_ok=True)
    require(shutil.disk_usage(root).free>2*1024**3,'INSUFFICIENT_DISK_SPACE')
    with tempfile.TemporaryDirectory(prefix='producer-build-',dir=root) as tmp:
        tmp=Path(tmp);unpacked=tmp/'source';unpacked.mkdir()
        directory='xorcyst-'+pin['release'];source=unpacked/directory
        with tarfile.open(fileobj=io.BytesIO(archive),mode='r:gz') as stream:
            names=set()
            for member in stream.getmembers():
                require(not member.name.startswith('/') and '..' not in Path(member.name).parts,
                        'PRODUCER_SOURCE_CHANGED')
                require(member.isfile() or member.isdir(),'PRODUCER_SOURCE_CHANGED')
                require(member.name not in names and
                        (member.name.startswith(directory+'/') or
                         (member.name==directory and member.isdir())), 'PRODUCER_SOURCE_CHANGED')
                names.add(member.name)
            stream.extractall(unpacked)
        require(digest((source/'doc/source-model.schema.json').read_bytes())==pin['schema_sha256'],'PRODUCER_SOURCE_CHANGED')
        commands=[['./configure','--disable-maintainer-mode','YACC=:','LEX=:','HELP2MAN=:',
                   'CFLAGS=-g -O2 -Werror'],['make','-j2']]
        with (tmp/'build.log').open('wb') as log:
            for command in commands:
                subprocess.run(command,cwd=source,stdout=log,stderr=subprocess.STDOUT,check=True)
        for name in ('xasm','xlnk'):
            version=subprocess.check_output([str(source/name),'--version'],text=True).strip()
            require(version==name+' '+pin['release'],'PRODUCER_VERSION_MISMATCH')
        binary=(source/'xasm').read_bytes();linker=(source/'xlnk').read_bytes();sha=digest(binary)
        destination=root/'toolchains'/sha
        recipe={'schema':'source-model-toolchain-v1','repository':pin['repository'],'commit':commit,
            'release':pin['release'],'archive_url':pin['archive_url'],'source_directory':directory,
            'producer_sha256':sha,'source_archive_sha256':digest(archive),'local_diff_sha256':digest(b''),
            'linker_sha256':digest(linker),
            'commands':commands,'compiler':subprocess.check_output(['cc','--version'],text=True),
            'source_schema_sha256':pin['schema_sha256']}
        for name,data in {'xasm':binary,'xlnk':linker,'source.tar.gz':archive,'local.patch':b'',
                'REBUILD-v2.json':json.dumps(recipe,sort_keys=True).encode()}.items():
            immutable_file(destination/name,data,0o755 if name in ('xasm','xlnk') else 0o644)
    return {'producer':str(destination/'xasm'),'producer_sha256':sha,
            'linker':str(destination/'xlnk'),'commit':commit,'release':pin['release'],
            'archive_sha256':pin['archive_sha256'],'store':str(root)}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path,required=True)
    parser.add_argument('--store',type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(build(args.archive,args.store)))
