"""Operator-only preparation; selection is supplied, never inferred by this CLI."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from . import gate_environment, producer, service as common, mixed_documents as mixed
from .launcher import Corridor
from .model import certify, digest
from .publication import configuration


def run(command, cwd, env, log):
    started=time.monotonic()
    with log.open('wb') as stream:
        result=subprocess.run(command,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    record={'command':command,'exit_code':result.returncode,'seconds':time.monotonic()-started,
            'log_sha256':producer.sha(log),'environment':dict(env)}
    if result.returncode:raise ValueError('PREPARATION_COMMAND_FAILED: '+str(log))
    return record


def prepare(repo, output, selection, executable, store):
    common.schema(selection,('project','target','objective','why_now','boundaries','evidence','reference_scope','out_of_scope'))
    producer.require(all(isinstance(v,str) and v.strip() for v in selection.values()),'PROJECT_SELECTION_INVALID')
    slug=selection['project'];producer.require(re.fullmatch('[a-z0-9_]+',slug),'PROJECT_SELECTION_INVALID')
    repo=Path(repo).resolve();root=Path(output).resolve()
    producer.require(not root.exists(),'PREPARATION_EXISTS')
    producer.EXE=Path(executable).resolve()
    configuration(producer.sha(producer.EXE),store)
    root.mkdir(parents=True)
    producer.require(shutil.disk_usage(root).free>3*1024**3,'INSUFFICIENT_DISK_SPACE')
    tools=gate_environment.configure(producer.EXE,root/'gate-home')
    env=gate_environment.environment(tools,root/'gate-tmp')
    base=common.git(repo,'rev-parse','HEAD',env=env)
    prefix='projects/'+slug+'/'
    producer.require(not common.git(repo,'diff','HEAD','--',prefix,env=env),'PROJECT_DIRTY')
    checkout=root/'checkout';logs=root/'logs';logs.mkdir()
    # Independent object storage: later GC in the operator checkout cannot remove
    # the prepared session's objects. No hardlinks to mutable project files.
    subprocess.run([tools['executables']['git'],'clone','-q','--no-hardlinks','--no-checkout',str(repo),str(checkout)],env=env,check=True)
    common.git(checkout,'checkout','--detach',base,env=env)
    loader='source scripts/project_common.sh\nload_project_conf "$1"\nprintf "%s\\0%s\\0" "$ASM_FILE" "$REF_NES"\n'
    result=subprocess.run([tools['executables']['bash'],'-c',loader,'project-loader',slug],cwd=checkout,env=env,capture_output=True,check=True)
    values=result.stdout.decode().split('\0')
    producer.require(len(values)==3 and values[-1]=='','PROJECT_PROFILE_INVALID')
    source,reference=values[:2]
    producer.require(all(v.startswith(prefix) and '..' not in Path(v).parts for v in values[:2]),'PROJECT_PROFILE_INVALID')
    # Refuse unsupported mixed documents before expensive preparation or creating a session.
    mixed.Scorecard((checkout/prefix/mixed.SCORECARD).read_bytes())
    mixed.deferral_rows((checkout/prefix/mixed.DEFERRALS).read_bytes())
    destination=checkout/reference;destination.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(repo/reference,destination)
    preparation=[run([tools['executables']['make'],'project-next-pass','PROJECT='+slug],checkout,env,logs/'next-pass.log')]
    fields={'CORRIDOR':'objective','WHY_NOW':'why_now','BOUNDARIES':'boundaries','EVIDENCE':'evidence',
            'REFERENCE_SCOPE':'reference_scope','OUT_OF_SCOPE':'out_of_scope'}
    preparation.append(run([tools['executables']['make'],'project-pass-start','PROJECT='+slug,'TARGET='+selection['target']]+
                           [key+'='+selection[value] for key,value in fields.items()],checkout,env,logs/'pass-start.log'))
    pass_dir=checkout/prefix/'docs/reverse_engineering/inventory/pass'
    plan=json.loads((pass_dir/'current_pass_plan.json').read_text())
    checks=[]
    for target in ('project-inventory','project-verify','project-process-check','project-docs-check'):
        checks.append({'target':target,**run([tools['executables']['make'],target,'PROJECT='+slug],checkout,env,logs/(target+'.log'))})
    changed=common.git(checkout,'diff','--name-only','HEAD',env=env).splitlines()
    producer.require(all(common.file_ownership(p,prefix,source)=='generated' for p in changed),'PREPARATION_CHANGED_AUTHORED_FILE')
    model,certificate=certify(checkout/source,root/'capture',checkout/reference)
    common.write_json(root/'baseline.json',{'checks':checks,'producer_sha256':producer.sha(producer.EXE)})
    profile={'schema':'current-project-profile-v1','slug':slug,'source':source,'reference':reference,
        'source_sha256':digest(model.source),'base_commit':base,'baseline_path':str(root/'baseline.json'),
        'baseline_sha256':producer.sha(root/'baseline.json'),'producer_path':str(producer.EXE),
        'producer_sha256':producer.sha(producer.EXE),'pass_id':str(plan['intended_pass_id']),
        'objective':selection['objective'],'next_pass_sha256':producer.sha(pass_dir/'next_pass.json'),
        'pass_plan_sha256':producer.sha(pass_dir/'current_pass_plan.json')}
    common.write_json(root/'profile.json',profile)
    controller=Corridor.initialize(root/'session',checkout,root/'capture',store,
        run_id=slug+'-structured-'+profile['pass_id'],objective=profile['objective'],project_profile=root/'profile.json')
    report={'project':slug,'pass_id':profile['pass_id'],'base_commit':base,'generation':controller.editor.state['current'],
            'certification':certificate,'checks':checks,'preparation':preparation,'provider_requests':0,'authorized':False}
    common.write_json(root/'preparation.json',report)
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ('repo','output','selection','producer','store'):parser.add_argument('--'+key,type=Path,required=True)
    args=parser.parse_args()
    result=prepare(args.repo,args.output,json.loads(args.selection.read_text()),args.producer,args.store)
    print(json.dumps({k:result[k] for k in ('project','pass_id','generation','provider_requests','authorized')}))


if __name__=='__main__':main()
