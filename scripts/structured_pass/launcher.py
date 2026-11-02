"""One bounded corridor controller: edit, gates, publication, review and archive.

The coordinator and its fixed-role bridges run outside source-free native client
workspaces. This controller uses an operator-pinned project and exposes only supported operations.
"""
import json
import fcntl
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
from .rename_service import RenameService
from . import service as common
from . import mixed_documents as mixed
from .structured_handoff import windows,require
from .verdict_bridge import Bridge
from .retained_service import RetainedReviewService
import process_friction

SCRIPTS=str(Path(process_friction.__file__).resolve().parent)
RETRYABLE={'VALIDATION_IN_PROGRESS','REVIEW_STATE_BUSY','REVIEW_RESTORE_IN_PROGRESS','HEAVY_RUN_IN_PROGRESS'}
ERRORS=frozenset('''CORRIDOR_NOT_PUBLISHED CORRIDOR_NOT_STARTED CORRIDOR_CONFIG_CHANGED
    CORRIDOR_RUN_CHANGED CORRIDOR_WRAPPER_REQUIRED REVIEWER_ONLY
    REVIEW_COVERAGE_INCOMPLETE CLOSEOUT_EVIDENCE_UNAVAILABLE HEAD_OWNED_BY_PUBLISHER
    BRIDGE_RUN_CHANGED PUBLISHER_BASE_MISMATCH PUBLISHER_STATE_UNAVAILABLE
    PUBLISHER_STORE_MISMATCH PUBLISHER_HEAD_MISMATCH PASS_BASE_NOT_ANCESTOR
    VERDICT_OUTSIDE_PASS CORRIDOR_OUTSIDE_PASS CORRIDOR_ROLE_INVALID REVIEW_ARCHIVE_EXISTS'''.split())
common.PUBLIC_ERROR_CODES|=ERRORS|frozenset(RETRYABLE)


class Corridor:
    def __init__(self,root):
        self.root=Path(root).resolve()
        self.config=json.loads((self.root/'session.json').read_text())
        require(self.config['schema']=='corridor-session-v1','CORRIDOR_CONFIG_CHANGED')
        require('project_profile' in self.config,'PROJECT_PROFILE_INVALID')
        editor_class=RenameService
        if 'project_profile' in self.config:
            from .current_project import service_class
            editor_class=service_class(self.config['project_profile'],self.config['project_profile_sha256'])
        self.editor=editor_class(self.root/'editor')
        self.review_sessions={}

    @classmethod
    def initialize(cls,root,base,capture,store,*,run_id,objective,project_profile=None):
        root=Path(root).resolve();root.mkdir(parents=True,exist_ok=False)
        require(project_profile is not None,'PROJECT_PROFILE_INVALID')
        editor_class=RenameService
        if project_profile is not None:
            from .current_project import service_class
            editor_class=service_class(project_profile)
        editor=editor_class.initialize(root/'editor',base,capture,base,retention_root=store)
        require(isinstance(objective,str) and bool(objective.strip()),'REQUEST_SCHEMA')
        with editor.transaction(write=True):
            editor.state['corridor']={'run_id':run_id,'objective':objective,
                'pass_start_generation':editor.state['pass_start_generation'],
                'pass_id':editor.document_pass_id()}
            editor.save()
        coordinator=root/'handoff';coordinator.mkdir()
        subprocess.run(['/usr/bin/git','init','-q',str(coordinator)],check=True)
        subprocess.run(['/usr/bin/git','-C',str(coordinator),'-c','user.name=Fixture',
            '-c','user.email=fixture@example.invalid','-c','commit.gpgsign=false','commit','-q',
            '--allow-empty','-m','Isolated corridor coordinator'],check=True)
        config={'schema':'corridor-session-v1','run_id':run_id,'objective':objective,
                'project':editor.slug,'pass_id':editor.document_pass_id(),'store':str(Path(store).resolve()),
                'pass_start_generation':editor.state['pass_start_generation']}
        if project_profile is not None:
            config.update(project_profile=str(Path(project_profile).resolve()),
                          project_profile_sha256=common.producer.sha(Path(project_profile)))
        common.write_json(root/'session.json',config)
        for role in ('implementer','reviewer'):
            common.write_json(root/(role+'-verdicts.json'),{'root':str(coordinator),'role':role,
                'run_id':run_id,'scripts':SCRIPTS})
        return cls(root)

    def checked_editor(self):
        self.editor.reload()
        start=self.editor.state['pass_start_generation']
        require(start==self.config['pass_start_generation'] and
            self.editor.state['corridor']['run_id']==self.config['run_id'], 'CORRIDOR_RUN_CHANGED')
        require(self.editor.state['corridor']['pass_id']==self.config['pass_id'] and
            self.editor.state['retention']['root']==self.config['store'],'CORRIDOR_CONFIG_CHANGED')
        return self.editor.state

    def verdicts(self,role):return Bridge(self.root/(role+'-verdicts.json'))

    def error_context(self,cid=None):return self.editor.error_context(cid)

    def ensure_handoff(self):
        with self.editor.transaction():
            state=self.checked_editor()
            current=state['generations'][state['current']].get('artifact')
            if current is None:return None
            base=state['generations'][state['pass_start_generation']]['artifact']['artifact_id']
            if not (self.root/'handoff/.agents/current.json').exists():
                command=[sys.executable,'-B',str(HERE.parent/'agent_review.py'),'--repo',str(self.root/'handoff'),
                    'init-structured','--project',self.config['project'],'--run-id',self.config['run_id'],
                    '--store',self.config['store'],'--base-artifact',base,'--head-artifact',current['artifact_id'],
                    '--reviewer','corridor-reviewer','--editor-state',str(self.editor.state_path)]
                result=subprocess.run(command,env={**os.environ,'PYTHONPATH':SCRIPTS,'PYTHONDONTWRITEBYTECODE':'1'},
                                      capture_output=True,text=True)
                if result.returncode:
                    code=result.stderr.strip().removeprefix('error: ')
                    raise ValueError(code)
            return current['artifact_id']

    def status(self,role):
        current_ticket=self.ensure_handoff()
        # Never decide approval from the saved current.json status.
        handoff=self.verdicts(role).command('status','--json') if current_ticket else None
        state=self.checked_editor();generation=state['current']
        return {'generation':generation,'run_id':self.config['run_id'],'objective':self.config['objective'],
                'pass_id':self.config['pass_id'],'pass_start_generation':state['pass_start_generation'],
                'ticket':current_ticket,'handoff':handoff,
                'scope':'Current project corridor; no quality verdict until independent review.'}

    def guidance(self,args):
        common.schema(args,('name',),('offset','limit'))
        names=['AGENTS.md']+['agent_playbook/'+name+'.md' for name in
            ('PASS_WORKFLOW','ASM_STYLE','QUALITY_REVIEW','REVIEW_AUDITS','TOOLING','DOCUMENTATION','DATA_RECOVERY')]
        require(args['name'] in names,'REQUEST_SCHEMA')
        offset=args.get('offset',0);limit=args.get('limit',200)
        require(type(offset) is int and offset>=0 and type(limit) is int and 1<=limit<=400,'REQUEST_SCHEMA')
        state=self.checked_editor()
        # Read the pinned pass-start policy, never arbitrary host paths or docs
        # supplied in a request. These are policies, not project source views.
        root=Path(state['generations'][state['pass_start_generation']]['checkout'])
        data=subprocess.check_output(['/usr/bin/git','-C',str(root),'show',
            self.editor.fixture['base_commit']+':'+args['name']])
        lines=data.decode().splitlines()
        return {'generation':state['current'],'path':args['name'],'sha256':common.digest(data),
                'policy_commit':self.editor.fixture['base_commit'],'total_lines':len(lines),'offset':offset,
                'lines':lines[offset:offset+limit],'next_offset':offset+limit if offset+limit<len(lines) else None}

    def review(self,args):
        common.schema(args,('ticket','generation','base_generation'),('offset','limit'))
        status=self.status('reviewer');require(status['handoff'] is not None,'CORRIDOR_NOT_PUBLISHED')
        known=status['handoff']['coverage']['required_edges']
        window=windows.window(self.config['store'],args['ticket'])
        require(all(edge in known for edge in window['edges']),'CORRIDOR_OUTSIDE_PASS')
        session=self.review_sessions.get(args['ticket'])
        if session is None:
            directory=self.root/'review-cache'/args['ticket']
            session=RetainedReviewService(directory) if directory.exists() else RetainedReviewService.from_publication(
                directory,self.config['store'],args['ticket'])
            self.review_sessions[args['ticket']]=session
        return session.review(args['generation'],args['base_generation'],args.get('offset',0),args.get('limit',1))

    def document(self,args):
        return self.generation_read('document',args)

    def generation_read(self,operation,args):
        specs={'document':(('generation','path'),('offset','limit')),
               'q09':(('generation','names'),('offset','limit')),
               'navigate':(('generation','view'),('symbol','record_id','contains','offset','limit'))}
        common.schema(args,*specs[operation])
        generation=args['generation']
        require(isinstance(generation,str),'REQUEST_SCHEMA')
        with self.editor.transaction():
            state=self.checked_editor()
            if generation.startswith('E-'):
                # Accept only artifacts on this pass's published ancestry. Do not
                # turn a read request into arbitrary retained-store access.
                current=state['current']
                while current is not None:
                    record=state['generations'][current]
                    if record.get('artifact',{}).get('artifact_id')==generation:break
                    if current==state['pass_start_generation']:current=None;break
                    current=record['base']
                require(current is not None,'UNKNOWN_GENERATION')
            else:current=generation
            result=self.editor.dispatch(operation,{**args,'generation':current},'reviewer')
            return {**result,'generation':generation}

    def closeout(self):
        with (self.editor.root/'validation.lock').open('rb') as lock:
            try:fcntl.flock(lock,fcntl.LOCK_SH|fcntl.LOCK_NB)
            except BlockingIOError:raise ValueError('VALIDATION_IN_PROGRESS') from None
            return self._closeout()

    def _closeout(self):
        require(self.ensure_handoff() is not None,'CORRIDOR_NOT_PUBLISHED')
        # The archive operation itself refreshes live coverage under both locks.
        # A later publication makes this exact-head receipt historical, not current approval.
        state=self.checked_editor();record=state['generations'][state['current']]
        head=record['artifact']['artifact_id']
        status=self.verdicts('implementer').command('status','--json')
        require(head==status['coverage']['pass_head'],'STALE_GENERATION')
        require(status['coverage']['coverage_complete'],'REVIEW_COVERAGE_INCOMPLETE')
        self.editor.model(state['current'])
        receipt=Path(record['capture'])/'closeout.json'
        require(receipt.is_file(),'CLOSEOUT_EVIDENCE_UNAVAILABLE')
        writer=json.loads(receipt.read_text())
        require(writer['gate']['exit_code']==0 and writer['closed_row']['verify']=='pass'
                and writer['closed_row']['docs_check']=='pass','CLOSEOUT_EVIDENCE_UNAVAILABLE')
        archive_args=['archive','--pass-id',self.config['pass_id']]
        relative='projects/'+self.config['project']+'/docs/reverse_engineering/reviews/pass-'+self.config['pass_id']+'.md'
        archive=self.root/'handoff'/relative
        if 'project_profile' in self.config and archive.exists():
            try:archived=json.loads(archive.read_text().split('```json\n',1)[1].split('\n```',1)[0])
            except (ValueError,IndexError):raise ValueError('REVIEW_ARCHIVE_EXISTS') from None
            require(archived==status,'REVIEW_ARCHIVE_EXISTS')
            answer={**status,'archive':relative}
        else:answer=self.verdicts('implementer').command(*archive_args)
        require(head==answer['coverage']['pass_head'],'STALE_GENERATION')
        answer={**answer,'wrapper_receipt_sha256':common.digest(receipt.read_bytes()),
                'archive_sha256':common.digest(archive.read_bytes()),
                'closed_generation':state['current'],'application':'Not applied or committed to the user checkout'}
        common.write_json(self.root/'closed.json',answer)
        return answer

    def dispatch(self,operation,arguments,role):
        require(role in ('implementer','reviewer'),'CORRIDOR_ROLE_INVALID')
        require(isinstance(operation,str) and isinstance(arguments,dict),'REQUEST_SCHEMA')
        self.checked_editor()
        if operation in ('approve','request-changes'):
            require(role=='reviewer','REVIEWER_ONLY')
            require(self.ensure_handoff() is not None,'CORRIDOR_NOT_PUBLISHED')
            return self.verdicts(role).dispatch({'operation':operation,'arguments':arguments})
        if operation in ('preview','confirm','validate','publish','start_chain','reready','closeout'):
            require(role=='implementer','REVIEWER_MUTATION_DENIED')
        if operation=='status':
            common.schema(arguments,());return self.status(role)
        if operation=='guidance':return self.guidance(arguments)
        if operation=='review':return self.review(arguments)
        if operation=='document':return self.document(arguments)
        if operation in ('q09','navigate'):return self.generation_read(operation,arguments)
        if operation=='closeout':
            common.schema(arguments,());return self.closeout()
        if operation=='reready':
            common.schema(arguments,('response',))
            require(isinstance(arguments['response'],str) and 0<len(arguments['response'])<=65536,'REQUEST_SCHEMA')
            require(self.ensure_handoff() is not None,'CORRIDOR_NOT_PUBLISHED')
            state=self.status(role);head=state['handoff']['coverage']['pass_head']
            folder=self.root/'handoff/.agents/runs'/self.config['run_id']
            with tempfile.NamedTemporaryFile(prefix='response-',suffix='.md',dir=folder,delete=False) as source:
                source.write(arguments['response'].encode());path=source.name
            return self.verdicts(role).command('reready','--head',head,'--response',path)
        if operation=='preview':
            common.schema(arguments,('generation','operations'),('cid',))
            require(isinstance(arguments['operations'],list) and all(isinstance(o,dict) for o in arguments['operations']),'REQUEST_SCHEMA')
            require(mixed.document_operations(arguments['operations']) is not None,'CORRIDOR_WRAPPER_REQUIRED')
        if operation=='publish':
            common.schema(arguments,('cid',))
            try:answer=self.editor.publish(arguments['cid'])
            except ValueError as exc:
                if str(exc)!='PUBLICATION_CHAIN_LIMIT':raise
                # Same validated candidate, no revalidation, resource window only.
                self.editor.start_chain(self.editor.state['current'])
                answer=self.editor.publish(arguments['cid'])
            self.ensure_handoff()
            return answer
        allowed={'candidate_status','navigate','inspect','query','q09','documents','document','preview','preview_page','confirm','validate','start_chain'}
        require(operation in allowed,'UNKNOWN_OPERATION')
        return self.editor.dispatch(operation,arguments,role)
