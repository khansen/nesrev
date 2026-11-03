"""Trusted coordinator application of a closed, approved generation; never an agent tool."""
import argparse
from contextlib import contextmanager
import fcntl
import json
from pathlib import Path
import subprocess
import tempfile

from .launcher import Corridor,common,require
from . import gate_environment
from . import structured_handoff
import agent_review


@contextmanager
def approved_application(controller):
    closed=controller.closeout()
    root=controller.root/'handoff'
    # Use the verdict command's lock order. Closeout runs before this transaction
    # because its subprocess also acquires the handoff lock.
    with structured_handoff.transaction(root):
        state=agent_review.read_state(root)
        config=state['structured_review']
        require(state['run_id']==controller.config['run_id'] and
                Path(config['editor_state']).resolve()==controller.editor.state_path.resolve(),
                'APPLICATION_APPROVAL_CHANGED')
        with structured_handoff.published_head(config) as head:
            approval=structured_handoff.result(agent_review,root,state)
            require(approval['status']=='APPROVED' and approval['coverage']['coverage_complete']
                    and head==approval['coverage']['pass_head']
                    and all(closed.get(k)==v for k,v in approval.items()),
                    'APPLICATION_APPROVAL_CHANGED')
            yield closed


def git(root,*args):
    return subprocess.check_output(['/usr/bin/git','-C',str(root),*args])


def hash_at(root,head,path):
    result=subprocess.run(['/usr/bin/git','-C',str(root),'show',head+':'+path],capture_output=True)
    return common.digest(result.stdout) if result.returncode==0 else None


def disk_hash(root,path):
    target=root/path
    require(target.resolve()==target.absolute() and not target.is_symlink(),'APPLICATION_PATH_FORBIDDEN')
    return common.producer.sha(target) if target.is_file() else None


def apply(session,target,*,commit=False):
    controller=Corridor(session);target=Path(target).resolve()
    with (controller.root/'application.lock').open('a+b') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        # Keep both the published head and its verdict fixed through the commit.
        with approved_application(controller) as closed:
            state=controller.checked_editor();head=state['current']
            require(common.producer.sha(target/controller.editor.reference)==state['reference_sha256'],
                    'APPLICATION_REFERENCE_CHANGED')
            base=state['generations'][state['pass_start_generation']];new=state['generations'][head]
            expected_branch='projects'
            require(git(target,'branch','--show-current').decode().strip()==expected_branch,'APPLICATION_BRANCH_CHANGED')
            current=git(target,'rev-parse','HEAD').decode().strip()
            paths=sorted(p for p in set(base['manifest'])|set(new['manifest'])
                         if base['manifest'].get(p)!=new['manifest'].get(p))
            archive=closed['archive'];require(archive not in paths,'APPLICATION_ARCHIVE_COLLISION')
            desired={p:new['manifest'].get(p) for p in paths};desired[archive]=closed['archive_sha256']
            journal=controller.root/'application.json'
            pending=json.loads(journal.read_text()) if journal.exists() else None
            if pending and pending.get('status')=='committed':
                require(pending['generation']==head and pending['target']==str(target),'APPLICATION_ALREADY_COMPLETED')
                recorded=pending['commit']
                require(all(hash_at(target,recorded,p)==h for p,h in desired.items()),'APPLICATION_COMMIT_CHANGED')
                return pending
            require(subprocess.run(['/usr/bin/git','-C',str(target),'merge-base','--is-ancestor',
                controller.editor.fixture['base_commit'],current],capture_output=True).returncode==0,'APPLICATION_BASE_DIVERGED')
            if pending and pending['head']!=current:
                # The commit can succeed immediately before a process/disk
                # failure prevents saving the final receipt. Recover that exact
                # approved commit rather than creating a second one.
                changed=set(git(target,'diff-tree','--no-commit-id','--name-only','-r',current).decode().splitlines())
                require(pending['generation']==head and pending['target']==str(target) and
                        git(target,'rev-parse',current+'^').decode().strip()==pending['head'] and
                        changed==set(desired) and all(hash_at(target,current,p)==h for p,h in desired.items()),
                        'APPLICATION_PENDING_CHANGED')
                result={**pending,'status':'committed','commit':current,'pushed':False}
                common.write_json(journal,result)
                return result
            if pending:
                require(pending['head']==current and pending['generation']==head and pending['target']==str(target),
                        'APPLICATION_PENDING_CHANGED')
            else:
                require(not (target/archive).exists() and hash_at(target,current,archive) is None,'REVIEW_ARCHIVE_EXISTS')
            unrelated=set(git(target,'diff','--name-only','HEAD','--',controller.editor.project).decode().splitlines())-set(desired)
            unrelated_hashes={p:disk_hash(target,p) for p in unrelated}
            staged=set(git(target,'diff','--cached','--name-only','-z').decode().split('\0'))-{''}
            require(not staged or pending and staged<=set(desired),'APPLICATION_INDEX_NOT_EMPTY')
            before={p:base['manifest'].get(p) for p in paths};before[archive]=None
            for path in desired:
                require(hash_at(target,current,path)==before[path],'APPLICATION_OVERLAPPING_CHANGE')
                actual=disk_hash(target,path)
                require(actual==before[path] or pending and actual==desired[path],'APPLICATION_DIRTY_PATH')
            plan={'status':'checked','target':str(target),'head':current,'generation':head,
                  'review_ticket':closed['coverage']['pass_head'],'paths':desired,
                  'archive':archive,'wrapper_receipt_sha256':closed['wrapper_receipt_sha256']}
            if not commit:return plan
            # A retry can finish this exact write set after a failed gate/signing
            # command. It cannot silently replace unrelated work or move the base.
            common.write_json(journal,{**plan,'status':'applying'})
            for path in desired:
                target_file=target/path;target_file.parent.mkdir(parents=True,exist_ok=True)
                if desired[path] is None:
                    if target_file.exists():target_file.unlink()
                    continue
                source=controller.root/'handoff'/archive if path==archive else Path(new['checkout'])/path
                data=source.read_bytes();require(common.digest(data)==desired[path],'GENERATION_INPUT_CHANGED')
                with tempfile.NamedTemporaryFile(dir=target_file.parent,delete=False) as temporary:
                    temporary.write(data);temporary_name=temporary.name
                Path(temporary_name).replace(target_file)
            evidence=controller.root/'application-gates';evidence.mkdir(exist_ok=True)
            env=gate_environment.environment(state['gate_toolchain'],evidence/'gate-tmp')
            gates=[]
            for name in ('project-inventory','project-verify','project-process-check','project-docs-check'):
                with (evidence/(name+'.log')).open('wb') as log:
                    result=subprocess.run([state['gate_toolchain']['executables']['make'],name,'PROJECT='+controller.editor.slug],
                        cwd=target,env=env,stdout=log,stderr=subprocess.STDOUT)
                gates.append({'target':name,'exit_code':result.returncode,
                              'log_sha256':common.producer.sha(evidence/(name+'.log'))})
                common.write_json(journal,{**plan,'status':'applying','gates':gates})
                require(result.returncode==0,'APPLICATION_GATE_FAILED')
            require(git(target,'rev-parse','HEAD').decode().strip()==current,'APPLICATION_HEAD_CHANGED')
            require(all(disk_hash(target,p)==h for p,h in desired.items()),'APPLICATION_APPROVED_FILES_CHANGED')
            # Gates must not change any other tracked path in this project.
            project_paths=set(git(target,'diff','--name-only','HEAD','--',controller.editor.project).decode().splitlines())
            require(project_paths-set(desired)==unrelated and
                    all(disk_hash(target,p)==h for p,h in unrelated_hashes.items()),'APPLICATION_UNEXPECTED_GATE_WRITE')
            git(target,'add','--',*desired)
            # Preserve the owner's identity; local pass commits are unsigned.
            git(target,'commit','--no-gpg-sign','--only','-m',f"Close {controller.editor.slug} pass {controller.config['pass_id']} through structured services",'--',*desired)
            committed=git(target,'rev-parse','HEAD').decode().strip()
            require(git(target,'rev-parse',committed+'^').decode().strip()==current,'APPLICATION_COMMIT_PARENT_CHANGED')
            require(all(hash_at(target,committed,p)==h for p,h in desired.items()),'APPLICATION_COMMIT_CHANGED')
            result={**plan,'status':'committed','commit':committed,'gates':gates,'pushed':False}
            common.write_json(journal,result)
            return result


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--session',type=Path,required=True)
    parser.add_argument('--repo',type=Path,required=True);parser.add_argument('--commit',action='store_true')
    args=parser.parse_args();print(json.dumps(apply(args.session,args.repo,commit=args.commit)))
