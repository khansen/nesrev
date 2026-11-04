"""Service-configured executables and an allowlisted environment for gates."""
import hashlib
import os
from pathlib import Path
import shutil
import sys

BASE_KEYS=frozenset(('PATH','HOME','TMPDIR','LC_ALL','LANG','XASM_BIN'))
CLOSEOUT_KEYS=frozenset(('PROJECT_PASS_CLOSEOUT_REPO_ROOT','FOCUS','NOTES','REWORK_ITEMS','DEFERRALS'))
ERRORS=frozenset(('GATE_TOOLCHAIN_UNAVAILABLE','GATE_TOOLCHAIN_CHANGED','GATE_ENVIRONMENT_INVALID'))


def require(condition,code='GATE_ENVIRONMENT_INVALID'):
    if not condition:raise ValueError(code)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def configure(xasm,home):
    # Prototype host tools are fixed paths, never selected via inherited PATH.
    tools={'xasm':Path(xasm).resolve(),'python3':Path(sys.executable).resolve(),
           'git':Path('/usr/bin/git'),'make':Path('/usr/bin/make'),'bash':Path('/bin/bash'),
           'rg':Path(shutil.which('rg') or '/usr/bin/rg').resolve()}
    require(all(p.is_file() and os.access(p,os.X_OK) for p in tools.values()),'GATE_TOOLCHAIN_UNAVAILABLE')
    # Keep writable build directories off PATH. Only the selected tools are
    # exposed in this service-owned directory; hash checks run before each gate.
    home=Path(home).resolve();home.mkdir()
    bindir=home/'gate-bin';bindir.mkdir()
    for name,executable in tools.items():
        (bindir/name).symlink_to(executable)
    path=os.pathsep.join((str(bindir),'/usr/bin','/bin'))
    return {'schema':'gate-toolchain-v1','executables':{k:str(v) for k,v in tools.items()},
            'sha256':{k:sha(v) for k,v in tools.items()},'path':path,'home':str(home)}


def environment(config,temporary):
    require(config['schema']=='gate-toolchain-v1')
    for name,path in config['executables'].items():
        require(Path(path).is_file() and sha(path)==config['sha256'][name],'GATE_TOOLCHAIN_CHANGED')
        selected=shutil.which(name,path=config['path'])
        require(selected is not None and Path(selected).resolve()==Path(path).resolve(),'GATE_TOOLCHAIN_CHANGED')
    temporary=Path(temporary).resolve();temporary.mkdir(parents=True,exist_ok=True)
    return {'PATH':config['path'],'HOME':config['home'],'TMPDIR':str(temporary),
            'LC_ALL':'C','LANG':'C','XASM_BIN':config['executables']['xasm']}


def closeout_environment(base,explicit):
    require(set(base)==BASE_KEYS and set(explicit)==CLOSEOUT_KEYS)
    require(all(isinstance(v,str) for v in explicit.values()))
    return {**base,**explicit}
