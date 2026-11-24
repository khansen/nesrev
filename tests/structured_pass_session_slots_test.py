"""Fresh profiles cannot reset shared invocation, identity or wall limits."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import session_slots as slots


class SessionSlotsTests(unittest.TestCase):
    def setUp(self):
        temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name).resolve();(self.root/'messages').mkdir()
        self.profiles={name:str(self.root/name) for name in ('first','second','implementer','reviewer')}
        self.config={'session_plan':{'investigators':[
            {'entry_id':name,'profile':self.profiles[name]} for name in ('first','second')],
            'editing_roles':['implementer','reviewer','implementer','reviewer','implementer']},
            'profiles':{k:self.profiles[k] for k in ('implementer','reviewer')},'run_id':'run','files':{}}
        for name,path in self.profiles.items():
            profile=Path(path);profile.mkdir()
            self.save(profile/'launch.json',{'pair_root':str(self.root)})
            self.save(profile/('budget.json' if name=='reviewer' else 'state.json'),
                      {'runs':[],'thread_id':None})
            self.config['files'][str(profile/'launch.json')]=slots.sha(profile/'launch.json')
        self.save(self.root/'launch.json',self.config)
        self.grant={'authorized':True,'owner_message':'Offline test','deadline':time.time()+300,
                    'max_invocations':7,'launch_sha256':slots.sha(self.root/'launch.json')}
        self.grant['profile_authorizations']={}
        self.grant['claude_responses']=40
        for name,path in self.profiles.items():
            profile=Path(path)
            if name=='reviewer':
                self.save(profile/'budget.json',{'runs':[],'thread_id':None,
                    'deadline':self.grant['deadline'],'max_responses':40})
            else:
                self.save(profile/'authorization.json',{'deadline':self.grant['deadline']})
                self.grant['profile_authorizations'][path]=slots.sha(profile/'authorization.json')
        self.save(self.root/'authorization.json',self.grant)
        self.state={'stop':None,'turns':[]}

    @staticmethod
    def save(path,value):path.write_text(json.dumps(value))

    def next(self):
        slot=slots.expected(self.config,self.state);index=len(self.state['turns'])
        profile=Path(slot['profile']);message=self.root/'messages'/(str(index)+'.txt')
        message.write_text('Read the assigned evidence.\n')
        record={'authority_sha256':slots.sha(self.root/'authorization.json'),
                'launch_sha256':slots.sha(profile/'launch.json'),'run_id':'run',
                'message_sha256':slots.sha(message)}
        self.save(message.with_suffix('.json'),record)
        row={**slot,'id':str(index),'message':str(message),'message_sha256':slots.sha(message),
             'result':'running','deadline':self.grant['deadline']}
        self.state['turns'].append(row);self.save(self.root/'state.json',self.state)
        return row

    def claim(self,row):
        return slots.claim(row['profile'],{'pair_root':str(self.root)},
            Path(row['message']).with_suffix('.json'),Path(row['message']).read_bytes(),row['role'])

    def complete(self,row):
        path=Path(row['profile'])/('state.json' if row['role']=='implementer' else 'budget.json')
        native=slots.read(path);native['thread_id']=native['thread_id'] or 'thread-'+row['id']
        native['runs'].append({'id':'client-'+row['id'],'status':'finished'})
        self.save(path,native);slots.finish(self.root,row)
        row['result']='checkpoint' if row['phase']=='investigation' else 'handoff'
        self.save(self.root/'state.json',self.state)

    def test_full_plan_keeps_counts_and_one_editor_context(self):
        threads=[]
        for _ in range(7):
            row=self.next();receipt=self.claim(row)
            self.assertEqual(receipt['slot_index'],int(row['id']))
            self.complete(row)
            if row['phase']=='editing' and row['role']=='implementer':threads.append(row['native_thread'])
        self.assertEqual(len(set(threads)),1)
        self.assertEqual(len(list((self.root/'claims').glob('*.json'))),7)
        with self.assertRaisesRegex(ValueError,'^INVOCATION_LIMIT$'):self.next()

    def test_one_claim_only_even_with_racing_adapters(self):
        row=self.next()
        def claim():
            try:self.claim(row);return 'accepted'
            except ValueError as exc:return str(exc)
        with ThreadPoolExecutor(max_workers=2) as pool:results=list(pool.map(lambda _:claim(),range(2)))
        self.assertCountEqual(results,['accepted','PAIR_ALREADY_STARTED'])

    def test_deadline_changed_message_profile_or_grant_cannot_admit(self):
        row=self.next();original=copy.deepcopy(self.state)
        for field,value in [('deadline',time.time()-1),('profile',self.profiles['second']),
                            ('entry_id','second'),('role','reviewer'),('phase','editing')]:
            self.state=copy.deepcopy(original);self.state['turns'][-1][field]=value
            self.save(self.root/'state.json',self.state)
            with self.subTest(field=field),self.assertRaises(ValueError):self.claim(row)
        self.state=original;self.save(self.root/'state.json',self.state)
        Path(row['message']).write_text('changed')
        with self.assertRaisesRegex(ValueError,'^PAIR_MESSAGE_CHANGED$'):self.claim(row)
        self.assertFalse((self.root/'claims').exists())

    def test_failed_slot_and_erased_client_history_do_not_reset_allowance(self):
        row=self.next();self.claim(row);row['result']='stopped';self.save(self.root/'state.json',self.state)
        with self.assertRaisesRegex(ValueError,'^PAIR_RECOVERY_REQUIRED$'):self.next()
        row['result']='running';self.complete(row)
        row=self.next();self.claim(row);self.complete(row)
        row=self.next();self.claim(row);self.complete(row)
        row=self.next();self.claim(row);self.complete(row)
        row=self.next()
        self.save(Path(row['profile'])/'state.json',{'runs':[],'thread_id':None})
        with self.assertRaisesRegex(ValueError,'^PAIR_RECOVERY_REQUIRED$'):self.claim(row)

    def test_adapter_extensions_cannot_change_the_shared_grant(self):
        row=self.next();profile=Path(row['profile'])
        value=slots.read(profile/'authorization.json');value['deadline']+=100
        self.save(profile/'authorization.json',value)
        with self.assertRaisesRegex(ValueError,'^PAIR_AUTHORIZATION_CHANGED$'):self.claim(row)

    def test_fresh_profile_cannot_bypass_message_slot(self):
        import structured_codex_client as codex
        row=self.next()
        with self.assertRaisesRegex(ValueError,'^PAIR_MESSAGE_CHANGED$'):
            slots.claim(row['profile'],{'pair_root':str(self.root)},None,b'anything','implementer')
        with patch.object(codex,'verify',return_value={'pair_root':str(self.root)}),\
                patch.object(codex,'admission',return_value={}),\
                patch.object(codex,'require_quiescent_runs'),patch.object(codex,'check_initial_editor'),\
                patch.object(codex,'phase_message',return_value=b'anything'),\
                patch.object(codex,'authenticate') as login:
            with self.assertRaisesRegex(ValueError,'^PAIR_MESSAGE_CHANGED$'):codex.run(Path(row['profile']))
            login.assert_not_called()
        from structured_pass import subscription_client as claude
        config={'pair_root':str(self.root),'heavy_lock':'test'}
        with patch.object(claude,'verify',return_value=config),\
                patch.dict(claude.os.environ,{'NESREV_HEAVY_RUN_LOCK':'test'}),\
                patch.object(claude,'authenticate') as login:
            with self.assertRaisesRegex(ValueError,'^PAIR_MESSAGE_CHANGED$'):
                claude.run_role(Path(self.profiles['reviewer']),'reviewer','anything')
            login.assert_not_called()


if __name__=='__main__':unittest.main()
