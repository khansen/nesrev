"""Declared input admission, integrity, independent restoration and role delivery."""
import base64
import copy
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import declared_inputs as inputs, guidance, producer, bridge, input_delivery
from structured_pass import subscription_client as claude
from structured_pass import navigation, analogue_inputs, startup_inputs
from structured_pass.launcher import Corridor
from structured_pass.model import certify
from structured_pass.retained_service import RetainedReviewService
import structured_codex_client as codex
from structured_pass_fixture import prepare, closeout_ops, git, SOURCE, REFERENCE


def setup_inputs(root,repo,analogues=False,startup=False):
    for name in guidance.NAMES:
        path=repo/name;path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text('# '+name+'\n<a id="current"></a>\n## Current\nPinned policy.\n'
                        '<a id="later"></a>\n## Later\nOn-demand policy.\n')
    review=repo/'projects/sample/docs/reverse_engineering/reviews/pass-0.md'
    review.parent.mkdir(parents=True);review.write_text('Verdict: APPROVED\nSTOP AFTER PASS 0\nGate evidence: naming-only.\n')
    reference=repo/'projects/sample/docs/game_reference/manual.pdf'
    reference.parent.mkdir(parents=True);reference.write_bytes(b'%PDF-synthetic reference')
    scratch=repo/'projects/sample/tmp';scratch.mkdir()
    text=scratch/'manual.txt';text.write_bytes(('Reference\r\n'+('é\\"\n'*2500)+'last').encode())
    empty=scratch/'empty.txt';empty.write_text('')
    image=scratch/'page.png';image.write_bytes(base64.b64decode('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+aD6cAAAAASUVORK5CYII='))
    items=[]
    for identity,kind,path in [('reference','reference_text',text),('empty','reference_text',empty),('page','reference_image',image)]:
        items.append({'id':identity,'kind':kind,'path':path.relative_to(repo).as_posix(),'sha256':producer.sha(path),
            'original_path':reference.relative_to(repo).as_posix(),'original_sha256':producer.sha(reference),
            'identity':{'pdf_page':1,'method':'synthetic test fixture'}})
    items.append({'id':'intake','kind':'intake_review','path':review.relative_to(repo).as_posix(),'sha256':producer.sha(review)})
    data={'historical':True,'verdict':'APPROVED'}
    items.append({'id':'receipt','kind':'intake_receipt','data':data,'sha256':producer.digest(inputs.canonical(data))})
    models=[];selected=[]
    if analogues:
        for index in range(2):
            source=repo/f'projects/analogue{index}/asm/source.asm';source.parent.mkdir(parents=True)
            data=(repo/SOURCE).read_bytes()
            source.write_bytes(data.replace(b'Cell',b'OtherCell') if index else data)
            model,_=certify(source,root/f'analogue-{index}',repo/REFERENCE)
            model_path=root/f'analogue-{index}/model.json';models.append(str(model_path))
            selected.append({'source':source.relative_to(repo).as_posix(),'sha256':producer.sha(source),'model_sha256':producer.sha(model_path)})
    git(repo,'add','.');git(repo,'commit','-qm','Synthetic declared inputs')
    spec={'schema':'declared-input-selection-v1','items':items,'analogues':selected}
    if startup:
        spec['startup']={'sections':[{'input_id':'guidance-0','anchors':['current']}],
            'context':{'window_tokens':258400,'startup_tokens':60000,'lifecycle_tokens':48000,
                       'margin_tokens':25840,'bytes_per_1000_tokens':2580}}
    path=root/'selection.json';path.write_text(json.dumps(spec))
    return {'selection':{'path':str(path),'sha256':producer.sha(path)},'analogue_models':models}


class AdmissionTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve();self.repo=self.root/'repo';self.repo.mkdir()
        git(self.repo,'init','-q')
        self.options=setup_inputs(self.root,self.repo)
        self.commit=git(self.repo,'rev-parse','HEAD')

    def admit(self,spec=None):
        option=self.options['selection']
        if spec is not None:
            path=self.root/'changed.json';path.write_text(json.dumps(spec))
            option={'path':str(path),'sha256':producer.sha(path)}
        target=self.root/'capture';target.mkdir(exist_ok=True)
        inputs.admit(self.repo,'sample',self.commit,option,target,[])
        return target

    def test_pagination_preserves_every_character_and_empty_input(self):
        target=self.admit();text=(self.repo/'projects/sample/tmp/manual.txt').read_bytes().decode()
        offset=0;pages=[]
        while True:
            page=inputs.read(target,'G-fixed','reference',offset,8192)
            self.assertLessEqual(inputs.review_pages.wire_size(page),24576)
            pages.append(page['text']);offset=page['next_offset']
            if offset is None:break
        self.assertEqual(''.join(pages),text);self.assertGreater(len(pages),1)
        empty=inputs.read(target,'G-fixed','empty')
        self.assertEqual(empty['text'],'');self.assertEqual(empty['total_characters'],0);self.assertIsNone(empty['next_offset'])
        (target/'input-empty.bin').write_text('x'*4096)
        catalog=json.loads((target/inputs.FILE).read_text())
        row=next(i for i in catalog['items'] if i['id']=='empty');row.update(sha256=producer.sha(target/'input-empty.bin'),bytes=4096)
        (target/inputs.FILE).write_bytes(inputs.canonical(catalog))
        full=inputs.read(target,'G-fixed','empty',limit=4096)
        self.assertEqual(len(full['text']),4096);self.assertIsNone(full['next_offset'])
        tail=inputs.read(target,'G-fixed','empty',offset=4094,limit=1)
        self.assertEqual(tail['text'],'x');self.assertEqual(tail['next_offset'],4095)
        last=inputs.read(target,'G-fixed','empty',offset=tail['next_offset'],limit=1)
        self.assertEqual(last['text'],'x');self.assertIsNone(last['next_offset'])

    def test_invalid_selection_and_paths_refuse_without_installing(self):
        original=json.loads(Path(self.options['selection']['path']).read_text())
        cases=[]
        for key,value in [('path','../../outside.txt'),('path','/etc/passwd'),
                          ('path','projects/sample/asm/source.asm'),('sha256','0'*64),
                          ('original_path','projects/other/docs/game_reference/manual.pdf')]:
            spec=copy.deepcopy(original);spec['items'][0][key]=value;cases.append(spec)
        duplicate=copy.deepcopy(original);duplicate['items'].append(duplicate['items'][0]);cases.append(duplicate)
        extra=copy.deepcopy(original);extra['items'][0]['command']='cat';cases.append(extra)
        rogue=copy.deepcopy(original);rogue['items'].append({'id':'rogue','kind':'comparison','path':'projects/other/docs/guide.md','sha256':'0'*64});cases.append(rogue)
        for spec in cases:
            with self.subTest(spec=spec['items'][0]):
                with self.assertRaises(ValueError):self.admit(spec)
                self.assertFalse((self.root/'capture'/inputs.FILE).exists())
        path=self.repo/'projects/sample/tmp/manual.txt';data=path.read_bytes();path.unlink()
        other=self.root/'outside.txt';other.write_bytes(data);path.symlink_to(other)
        with self.assertRaises(ValueError):self.admit()
        path.unlink();path.write_bytes(data)
        selection=Path(self.options['selection']['path']);selection.write_text(selection.read_text()+' ')
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):self.admit()

    def test_missing_changed_and_undeclared_inputs_refuse(self):
        target=self.admit()
        with self.assertRaisesRegex(ValueError,'INPUT_UNKNOWN'):inputs.read(target,'G-fixed','/etc/passwd')
        with self.assertRaisesRegex(ValueError,'INPUT_MEDIA_REQUIRED'):inputs.read(target,'G-fixed','page')
        path=target/'input-reference.bin';original=path.read_bytes();path.write_bytes(b'X'+original[1:])
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):inputs.read(target,'G-fixed','reference')
        path.write_bytes(original);path.unlink()
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):inputs.read(target,'G-fixed','empty')

    def test_limits_and_historical_authority_are_explicit(self):
        with patch.object(inputs,'TEXT_TOTAL',1):
            with self.assertRaisesRegex(ValueError,'INPUT_LIMIT_EXCEEDED'):self.admit()
        target=self.admit();page=inputs.read(target,'G-fixed','intake')
        self.assertTrue(page['historical']);self.assertEqual(page['authority'],inputs.HISTORICAL)
        self.assertIn('STOP AFTER PASS 0',page['text'])
        self.assertEqual(inputs.guidance_bytes(target,'agent_playbook/NEW_PROJECT.md'),
                         (self.repo/'agent_playbook/NEW_PROJECT.md').read_bytes())

    def test_operator_selection_boundaries(self):
        original=json.loads(Path(self.options['selection']['path']).read_text())
        other=self.repo/'projects/sample/docs/reference.txt';other.write_text('Evidence')
        spec=copy.deepcopy(original);spec['items'][0].update(
            path='projects/sample/tmp/../docs/reference.txt',sha256=producer.sha(other))
        with self.assertRaisesRegex(ValueError,'INPUT_SELECTION_INVALID'):self.admit(spec)
        review=next(i for i in original['items'] if i['kind']=='intake_review')
        other=self.repo/'projects/sample/docs/reverse_engineering/reviews/pass-9.md'
        other.write_bytes((self.repo/review['path']).read_bytes())
        git(self.repo,'add','.');git(self.repo,'commit','-qm','Synthetic alternate archive')
        self.commit=git(self.repo,'rev-parse','HEAD')
        spec=copy.deepcopy(original);next(i for i in spec['items'] if i['kind']=='intake_review')['path']=other.relative_to(self.repo).as_posix()
        with self.assertRaisesRegex(ValueError,'INPUT_SELECTION_INVALID'):self.admit(spec)
        with patch.object(inputs,'TEXT_LIMIT',10):
            with self.assertRaisesRegex(ValueError,'INPUT_LIMIT_EXCEEDED'):self.admit()
        for kind,count in (('reference_text',33),('reference_image',17)):
            entry=next(i for i in original['items'] if i['kind']==kind)
            spec=copy.deepcopy(original);spec['items']=[{**entry,'id':'item-'+str(n)} for n in range(count)]
            with self.assertRaisesRegex(ValueError,'INPUT_LIMIT_EXCEEDED'):self.admit(spec)
        link=self.repo/'link.md';link.symlink_to(other)
        git(self.repo,'add','link.md');git(self.repo,'commit','-qm','Synthetic symlink blob')
        with self.assertRaisesRegex(ValueError,'INPUT_SELECTION_INVALID'):
            inputs.committed(self.repo,git(self.repo,'rev-parse','HEAD'),'link.md')


class LifecycleTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.tmp=tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='inputs-test-');self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.c=prepare(self.root,declared_setup=lambda root,repo:setup_inputs(root,repo,True,True))
        self.g=self.c.editor.state['current']

    def call(self,root,role,operation,args,profile='corridor'):
        request={'id':1,'method':'tools/call','params':{'name':'operation','arguments':{'operation':operation,'arguments':args}}}
        result=io.StringIO();bridge.mcp(root,role,profile,io.StringIO(json.dumps(request)+'\n'),result)
        wire=result.getvalue();self.assertLessEqual(len(wire.encode()),24576)
        answer=json.loads(wire)['result'];self.assertFalse(answer.get('isError'),answer)
        return json.loads(answer['content'][0]['text'])

    def collect(self,root,role,generation,input_id,profile='corridor'):
        offset=0;result=''
        while True:
            page=self.call(root,role,'input',{'generation':generation,'input_id':input_id,'offset':offset},profile)
            result+=page['text'];offset=page['next_offset']
            if offset is None:return result

    def test_complete_inputs_both_roles_and_retained_after_originals_removed(self):
        expected=(self.root/'repo/projects/sample/tmp/manual.txt').read_bytes().decode()
        operation_reference=self.collect(self.c.root,'implementer',self.g,'operation-reference')
        def check_edit_sources(text):
            reference=json.loads(text)
            self.assertIn('edit',reference['view_arguments']['navigate']['views'])
            self.assertIn('preimages array',reference['view_arguments']['navigate']['edit']['decode'])
            for table,fields in [('rename_fields',('declaration_id','old_name','preimage')),
                    ('source_edit_fields',('anchor_id','declaration_id','scope_id','expression_id',
                                          'preimage','record_ids','preimages','groups'))]:
                for field in fields:
                    self.assertIn('navigate(view=edit)',reference['types'][table][field]['source'])
        check_edit_sources(operation_reference)
        self.assertEqual(json.loads(operation_reference)['question_budget']['text_response_bytes'],409600)
        for role in ('implementer','reviewer'):
            delivered=self.collect(self.c.root,role,self.g,'operation-reference')
            self.assertEqual(delivered,operation_reference)
            check_edit_sources(delivered)
            self.assertIn('409600 bytes',json.loads(delivered)['request_counting'])
            self.assertIn('missing allowance requires a decision',json.loads(delivered)['question_budget']['conversation_allowance'])
            selected=self.collect(self.c.root,role,self.g,startup_inputs.INPUT_ID)
            self.assertIn('Pinned policy.',selected);self.assertNotIn('On-demand policy.',selected)
            self.assertIn('On-demand policy.',self.collect(self.c.root,role,self.g,'guidance-0'))
            self.assertEqual(self.collect(self.c.root,role,self.g,'reference'),expected)
            catalog=self.call(self.c.root,role,'inputs',{'generation':self.g,'limit':40})
            guide=next(row for row in catalog['records'] if row['kind']=='guidance'
                       and row['origin']['path']=='agent_playbook/NEW_PROJECT.md')
            self.assertIn('Pinned policy.',self.collect(self.c.root,role,self.g,guide['id']))
            with self.assertRaisesRegex(ValueError,'UNKNOWN_OPERATION'):
                self.c.dispatch('guidance',{'name':'agent_playbook/NEW_PROJECT.md'},role)
        notes='projects/sample/docs/reverse_engineering/WORKING_NOTES.md'
        original=self.c.editor.document(self.g,notes)
        ops=[{'kind':'document_write','path':notes,'preimage':original['preimage'],'text':'# Notes\n\nUpdated durable evidence.\n','reason':'Preserve the synthetic evidence conclusion.'},*closeout_ops(self.c,self.g)]
        preview=self.c.dispatch('preview',{'generation':self.g,'operations':ops},'implementer')
        cid=self.c.dispatch('confirm',{'generation':self.g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
        self.assertEqual(self.c.dispatch('validate',{'cid':cid},'implementer')['status'],'validated')
        pub=self.c.dispatch('publish',{'cid':cid},'implementer');ticket=pub['review']['artifact_id']
        (self.root/'selection.json').rename(self.root/'selection.removed')
        for path in ('tmp','docs/game_reference'):
            shutil.rmtree(self.root/'repo/projects/sample'/path)
        restored=RetainedReviewService.from_publication(self.root/'restored',self.c.config['store'],ticket)
        self.assertEqual(self.collect(restored.root,'reviewer',ticket,'reference','retained'),expected)
        self.assertEqual(self.collect(restored.root,'reviewer',ticket,startup_inputs.INPUT_ID,'retained'),selected)
        delivered=self.collect(restored.root,'reviewer',ticket,'operation-reference','retained')
        self.assertEqual(delivered,operation_reference)
        check_edit_sources(delivered)
        self.assertEqual(json.loads(delivered)['question_budget']['text_response_bytes'],409600)
        self.assertIn('missing allowance requires a decision',json.loads(delivered)['question_budget']['conversation_allowance'])
        archive=self.call(restored.root,'reviewer','input',{'generation':ticket,'input_id':'intake'},'retained')
        self.assertTrue(archive['historical']);self.assertEqual(archive['authority'],inputs.HISTORICAL)
        self.assertIn('STOP AFTER PASS 0',archive['text'])
        self.assertTrue(self.call(restored.root,'reviewer','guidance',{'generation':ticket,'name':'agent_playbook/NEW_PROJECT.md'},'retained')['lines'])
        self.assertIn('Updated durable evidence.',self.call(restored.root,'reviewer','document',{'generation':ticket,'path':notes},'retained')['lines'])
        for bad in ('G-stale','E-'+'0'*64):
            with self.assertRaisesRegex(ValueError,'UNKNOWN_GENERATION'):
                self.c.dispatch('input',{'generation':bad,'input_id':'reference'},'reviewer')

    def test_analogue_navigation_identity_and_root_boundaries(self):
        model=self.c.editor.model(self.g)
        for index in (0,1):
            selected=analogue_inputs.project(model,index)
            for role in ('implementer','reviewer'):
                page=self.call(self.c.root,role,'navigate',{'generation':self.g,'view':'records','symbol':'Entry','analogue_index':index,'limit':2})
                self.assertEqual(page['analogue_model_id'],selected.document['identity']['model_id'])
                self.assertEqual(page['records'],navigation.Navigation(selected).query('records',symbol='Entry',limit=2)['records'])
        for index in (-1,2,True,'0'):
            with self.assertRaises(ValueError):self.c.dispatch('navigate',{'generation':self.g,'view':'records','symbol':'Entry','analogue_index':index},'reviewer')
        for path in ('README.md','WORKING_NOTES.md','PROCESS_FRICTION.md','asm/sample.asm'):
            with self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):
                self.c.dispatch('document',{'generation':self.g,'path':'projects/sample/'+path},'reviewer')

    def test_profile_and_capture_input_manifest_cannot_be_replaced(self):
        profile=self.root/'profile.json';original=profile.read_bytes();data=json.loads(original)
        data['declared_inputs_sha256']='0'*64;profile.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError,'PROJECT_PROFILE_CHANGED'):Corridor(self.c.root)
        profile.write_bytes(original)
        capture=self.c.editor.model(self.g).capture;path=capture/inputs.FILE;raw=path.read_bytes()
        path.write_bytes(raw+b' ')
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED|CAPTURE_CHANGED'):
            self.c.dispatch('inputs',{'generation':self.g},'reviewer')

    def test_assembled_roles_label_history_and_preserve_page_identity(self):
        task='Complete only pass 1; stop after independent review and closeout.'
        for role in ('implementer','reviewer'):
            folder=self.root/('assembled-'+role)
            record=input_delivery.assemble(self.c.root,folder,role,task)
            text=input_delivery.prompt(record,self.root/('workspace-'+role))
            self.assertIn('Current authorized pass scope',text);self.assertIn(task,text)
            self.assertIn(inputs.HISTORICAL,text);self.assertNotIn('STOP AFTER PASS 0',text)
            self.assertEqual(len(record['items']),16);self.assertEqual(len(record['media']),1)
            self.assertIn('321364 bytes',text)
            self.assertIn('guidance-startup completely at startup',text)
            self.assertEqual(record['media'][0]['origin']['identity']['pdf_page'],1)
            path=folder/'assembly.json';original=path.read_bytes()
            for mutate in ('omit','page','media_hash','pass','missing_budget','inflated_budget'):
                changed=json.loads(original)
                if mutate=='omit':changed['items'].pop()
                elif mutate=='page':changed['media'][0]['origin']['identity']['pdf_page']=2
                elif mutate=='media_hash':changed['media'][0]['sha256']='0'*64
                elif mutate=='pass':changed['pass_id']='2'
                elif mutate=='missing_budget':del changed['startup']
                else:changed['startup']['budget']['response_bytes']+=1
                path.write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):input_delivery.verify(self.c.root,path)
            path.write_bytes(original)

    def test_adapter_assemblies_offline_with_stub_clients(self):
        task='Authorized pass 1: synthetic corridor; stop after its review.'
        prompts=self.root/'prompts';prompts.mkdir()
        for role in ('implementer','reviewer'):(prompts/(role+'.md')).write_text('Use only the facts bridge.\n')
        client=self.root/'fake-client';client.write_text('#!/bin/sh\necho offline-fixture\n');client.chmod(0o755)
        host=self.root/'codex-code-mode-host';host.write_text('fixture')
        c=claude.prepare(self.root/'claude',self.c.root,prompts,model='fixture',effort='high',
                         client=client,interpreter=sys.executable,heavy_lock=self.root/'lock',task=task)
        self.addCleanup(shutil.rmtree,Path(c['roles']['reviewer']['workspace']).parent)
        external=tempfile.TemporaryDirectory(prefix='inputs-client-');self.addCleanup(external.cleanup)
        codex_root=Path(external.name)/'codex'
        d=codex.prepare(codex_root,session=self.c.root,prompt=prompts/'implementer.md',model='fixture',effort='high',
                        client=client,interpreter=sys.executable,service_root=ROOT,heavy_lock=self.root/'lock',message=task)
        for profile in (c['roles']['reviewer'],d):
            prompt_path=Path(profile.get('prompt',codex_root/'prompt.md'))
            self.assertIn(inputs.HISTORICAL,prompt_path.read_text());self.assertIn(task,prompt_path.read_text())
            self.assertIn('321364 bytes',prompt_path.read_text())
            self.assertIn('guidance-startup completely at startup',prompt_path.read_text())
            self.assertNotIn('STOP AFTER PASS 0',prompt_path.read_text())
            self.assertEqual(len(profile['media']),1 if profile is c['roles']['reviewer'] else 0)
            self.assertEqual(json.loads(Path(profile['input_assembly']).read_text())['items'],
                             [inputs.metadata(i) for i in inputs.load(self.c.editor.model(self.g).capture)['items']])
        self.assertEqual(list(Path(d['workspace']).iterdir()),[])
        config=json.loads((codex_root/'config.json').read_text())
        self.assertFalse(config['features']['view_image'])
        self.assertFalse(config['features']['shell_tool'])
        self.assertFalse(config['features']['code_mode']['enabled'])
        self.assertEqual(json.loads((codex_root/'policy.json').read_text())['media'],{})
        self.assertIn(inputs.IMAGE_GUIDANCE,(codex_root/'prompt.md').read_text())
        self.assertNotIn(str(Path(d['workspace'])/'page.png'),(codex_root/'prompt.md').read_text())
        claude.verify(self.root/'claude');codex.verify(codex_root)


class NotesAdvisoryTests(unittest.TestCase):
    def test_real_advisory_branch_warns_without_failure(self):
        # Run the production block with the rest of the gate replaced by a success control.
        text=(ROOT/'scripts/project_process_check.sh').read_text()
        start=text.index('echo "[1/4] Checking required process artifacts"')
        end=text.index('python3 "${SCRIPT_DIR}/project_artifact_manifest.py"',start)
        block=text[start:end]
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);project=root/'projects/sample';project.mkdir(parents=True)
            canonical=project/'docs/reverse_engineering/WORKING_NOTES.md';canonical.parent.mkdir(parents=True)
            for root_exists,canonical_exists in ((False,False),(False,True),(True,False),(True,True)):
                for path,exists in ((project/'WORKING_NOTES.md',root_exists),(canonical,canonical_exists)):
                    if exists:path.write_text('Notes')
                    else:path.unlink(missing_ok=True)
                result=subprocess.run(['/bin/bash','-c','set -euo pipefail\n'+block,'fixture','sample'],cwd=root,capture_output=True,text=True)
                self.assertEqual(result.returncode,0)
                self.assertEqual('advisory:' in result.stderr,root_exists)
                if root_exists:self.assertIn('docs/reverse_engineering/WORKING_NOTES.md',result.stderr)


if __name__=='__main__':unittest.main()
