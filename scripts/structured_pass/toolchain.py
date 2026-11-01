"""Operator-only build of the pinned producer, retained with its source recipe."""
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


def build(repository, store_root):
    repository=Path(repository).resolve();root=persistent_root(store_root)
    root.mkdir(parents=True,exist_ok=True)
    require(shutil.disk_usage(root).free>2*1024**3,'INSUFFICIENT_DISK_SPACE')
    pin=json.loads(PIN.read_text());commit=pin['commit']
    actual=subprocess.check_output(['git','-C',str(repository),'rev-parse',commit+'^{commit}'],text=True).strip()
    require(actual==commit,'PRODUCER_SOURCE_CHANGED')
    archive=subprocess.check_output(['git','-C',str(repository),'archive','--format=tar.gz',commit])
    with tempfile.TemporaryDirectory(prefix='producer-build-',dir=root) as tmp:
        tmp=Path(tmp);source=tmp/'source';source.mkdir()
        package=tmp/'source.tar.gz';package.write_bytes(archive)
        with tarfile.open(package) as stream:
            for member in stream.getmembers():
                require(not member.name.startswith('/') and '..' not in Path(member.name).parts,
                        'PRODUCER_SOURCE_CHANGED')
                require(member.isfile() or member.isdir(),'PRODUCER_SOURCE_CHANGED')
            stream.extractall(source)
        require(digest((source/'doc/source-model.schema.json').read_bytes())==pin['schema_sha256'],'PRODUCER_SOURCE_CHANGED')
        commands=[['./configure','--disable-maintainer-mode','YACC=:','LEX=:','HELP2MAN=:'],['make','-j2']]
        with (tmp/'build.log').open('wb') as log:
            for command in commands:
                subprocess.run(command,cwd=source,stdout=log,stderr=subprocess.STDOUT,check=True)
        binary=(source/'xasm').read_bytes();sha=digest(binary)
        destination=root/'toolchains'/sha
        recipe={'schema':'source-model-toolchain-v1','repository':pin['repository'],'commit':commit,
            'producer_sha256':sha,'source_archive_sha256':digest(archive),'local_diff_sha256':digest(b''),
            'commands':commands,'compiler':subprocess.check_output(['cc','--version'],text=True),
            'source_schema_sha256':pin['schema_sha256']}
        for name,data in {'xasm':binary,'source.tar.gz':archive,'local.patch':b'',
                'REBUILD-v2.json':json.dumps(recipe,sort_keys=True).encode()}.items():
            immutable_file(destination/name,data,0o755 if name=='xasm' else 0o644)
    return {'producer':str(destination/'xasm'),'producer_sha256':sha,'commit':commit,'store':str(root)}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--store',type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(build(args.repo,args.store)))
