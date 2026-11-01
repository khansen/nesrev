"""One owner-approved allowance shared by both roles, including retries/rework."""
from contextlib import contextmanager
import fcntl
import json
from pathlib import Path
import time
import uuid

from .service import write_json


def require(value,code):
    if not value:raise ValueError(code)


class Budget:
    def __init__(self,root,configuration_hash):
        self.root=Path(root);self.configuration_hash=configuration_hash

    @contextmanager
    def transaction(self):
        with (self.root/'budget.lock').open('a+b') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            state=json.loads((self.root/'budget.json').read_text())
            require(state['configuration_sha256']==self.configuration_hash,'LAUNCH_CONFIGURATION_CHANGED')
            yield state
            write_json(self.root/'budget.json',state)

    def reserve(self,role,requested):
        require(role in ('implementer','reviewer') and type(requested) is int and requested>0,'BUDGET_REQUEST_INVALID')
        with self.transaction() as state:
            require(state.get('authorized') is True,'INFERENCE_NOT_AUTHORIZED')
            require(not any(r['status']=='running' for r in state['runs']),'ROLE_ALREADY_RUNNING')
            require(not state.get('halted'),'BUDGET_HALTED')
            now=time.time()
            if state.get('deadline') is None:state['deadline']=now+state['max_seconds']
            require(now<state['deadline'],'RUN_TIME_LIMIT')
            remaining=state['max_responses']-sum(r['charged'] for r in state['runs'])
            require(remaining>0,'RESPONSE_LIMIT')
            count=min(remaining,requested)
            # Reserve admission capacity separately from observed usage. A dead
            # owner leaves a running reservation which blocks automatic resume.
            item={'id':uuid.uuid4().hex,'role':role,'reserved':count,'charged':0,'response_ids':[],
                  'status':'running','started':now,'deadline':state['deadline']}
            state['runs'].append(item)
            return dict(item)

    @staticmethod
    def record_responses(state,row,events):
        prior={identifier for run in state['runs'] if run is not row for identifier in run.get('response_ids',[])}
        ids=set(row['response_ids'])
        for event in events:
            if event.get('type')!='assistant':continue
            message=event.get('message')
            require(isinstance(message,dict) and isinstance(message.get('id'),str) and bool(message['id']),
                    'RESPONSE_ID_UNAVAILABLE')
            if message['id'] not in prior:ids.add(message['id'])
        row.update(response_ids=sorted(ids),charged=len(ids),observed_responses=len(ids),
                   accounting='distinct_assistant_message_ids')

    def observe(self,identifier,event):
        """Persist each response before accepting another streamed event."""
        with self.transaction() as state:
            row=next(r for r in state['runs'] if r['id']==identifier)
            require(row['status']=='running','BUDGET_RUN_ALREADY_FINISHED')
            self.record_responses(state,row,[event])
            exceeded=row['charged']>row['reserved']
            if exceeded:state['halted']=True;row['error']='CLIENT_RESPONSE_LIMIT_BROKEN'
        require(not exceeded,'CLIENT_RESPONSE_LIMIT_BROKEN')

    def finish(self,identifier,events,*,timeout=False):
        with self.transaction() as state:
            row=next(r for r in state['runs'] if r['id']==identifier)
            require(row['status']=='running','BUDGET_RUN_ALREADY_FINISHED')
            self.record_responses(state,row,events)
            finals=[e for e in events if e.get('type')=='result']
            complete=len(finals)==1 and not timeout
            row.update(status='finished' if complete else 'interrupted',finished=time.time(),
                       timeout=timeout,usage_uncertain=not complete)
            if finals:row['client_num_turns']=finals[-1].get('num_turns')
            if finals:row['usage']=finals[-1].get('usage',{});row['result_subtype']=finals[-1].get('subtype')
            if not complete or row['charged']>row['reserved']:
                state['halted']=True
                row['error']=('RUN_TIME_LIMIT' if timeout else 'CLIENT_RESPONSE_LIMIT_BROKEN'
                              if row['charged']>row['reserved'] else 'INCOMPLETE_USAGE_REQUIRES_RECOVERY')
            return dict(row)

    def interrupt(self,identifier):
        with self.transaction() as state:
            row=next(r for r in state['runs'] if r['id']==identifier)
            require(row['status']=='running','BUDGET_RUN_ALREADY_FINISHED')
            row.update(status='interrupted',finished=time.time(),usage_uncertain=True)
            state['halted']=True  # Keep observed usage; require explicit owner recovery.

    def extend(self,responses,seconds,reason,*,recover_interrupted=False):
        """Owner command only. The caller holds the shared heavy-run lock.

        That runner has reaped earlier invocations (or refuses for live
        orphans), so a leftover running reservation may be marked interrupted.
        Its observed charges remain. Uncertain usage is recorded for the owner;
        no model/bridge operation can release that stop.
        """
        require(type(responses) is int and responses>=0 and type(seconds) is int and seconds>=0
                and responses+seconds>0,'INVALID_BUDGET')
        require(isinstance(reason,str) and 0<len(reason.strip())<=2000,'EXTENSION_REASON_REQUIRED')
        with self.transaction() as state:
            require(state.get('authorized') is True,'INFERENCE_NOT_AUTHORIZED')
            running=[r for r in state['runs'] if r['status']=='running']
            require(not running or recover_interrupted,'ROLE_ALREADY_RUNNING')
            now=time.time()
            before={k:state.get(k) for k in ('max_responses','max_seconds','deadline','halted')}
            for row in running:row.update(status='interrupted',finished=now,usage_uncertain=True,error='OWNER_RECOVERED_INTERRUPTED_RUN')
            state['max_responses']+=responses;state['max_seconds']+=seconds
            if seconds and state.get('deadline') is not None:
                state['deadline']=max(now,state['deadline'])+seconds
            state['halted']=False
            history=state.setdefault('extensions',[])
            event={'sequence':len(history)+1,'approved_at':now,'reason':reason.strip(),
                   'added_responses':responses,'added_seconds':seconds,'before':before,
                   'after':{k:state.get(k) for k in before},
                   'charged_responses_preserved':sum(r['charged'] for r in state['runs']),
                   'recovered_runs':[r['id'] for r in running],
                   'uncertain_usage_runs':[r['id'] for r in state['runs'] if r.get('usage_uncertain')]}
            history.append(event)
            return dict(event)
