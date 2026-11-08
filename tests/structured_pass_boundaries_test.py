"""Boundary, transaction and ownership controls without producer runs."""
import copy
import csv
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'scripts'))
from structured_pass import service
from structured_pass import authored_documents as docs
from structured_pass import review_pages


class Documents(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve();self.project='projects/demo/';self.source=self.project+'asm/demo.asm'
        self.path=self.project+'docs/reverse_engineering/WORKING_NOTES.md'
        target=self.root/self.path;target.parent.mkdir(parents=True);target.write_text('Before\n')
        self.manifest={self.path:docs.sha(target.read_bytes())}

    def op(self,**changes):
        return {'kind':'document_write','path':self.path,'preimage':self.manifest[self.path],
                'text':'After\n','reason':'Synthetic document operation',**changes}

    def ownership(self,path,project,source):
        registered=['docs/reverse_engineering/'+name for name in (
            'OPTIONAL.md','Demo_DX_Systems.md','Guides/NEW.md','Guides/EXISTING.md',
            'NewDirectory/A.md','NewDirectory/B.md')]
        return service.file_ownership(path,project,source,registered)

    def prepare(self,ops):return docs.prepare(self.root,self.manifest,ops,self.project,self.source,self.ownership)

    def test_existing_new_deleted_documents_and_preimages(self):
        result=self.prepare([self.op()]);self.assertEqual(result[0]['before'],b'Before\n')
        self.assertEqual(result[0]['after'],b'After\n')
        new=self.op(path=self.project+'docs/reverse_engineering/OPTIONAL.md',preimage=None)
        self.assertIsNone(self.prepare([new])[0]['before'])
        delete={k:v for k,v in self.op(kind='document_delete').items() if k!='text'}
        self.assertIsNone(self.prepare([delete])[0]['after'])
        with self.assertRaisesRegex(ValueError,'DOCUMENT_PREIMAGE_MISMATCH'):self.prepare([self.op(preimage=None)])

    def test_document_hunks_preserve_edits_and_absent_sides(self):
        for before,after,old,new,start in (
                (b'prefix\nold\ntail\n',b'prefix\nnew\ntail\n',['old'],['new'],2),
                (b'prefix\nremoved\ntail\n',b'prefix\ntail\n',['removed'],[],2),
                (None,b'added\n',None,['added'],1),
                (b'deleted\n',None,['deleted'],None,1)):
            with self.subTest(before=before,after=after):
                value=docs.describe({'before':before,'after':after,'path':self.path,'reason':'Fixture'})
                self.assertEqual(value['total_hunks'],1);self.assertEqual(value['omitted_hunks'],0)
                for side,lines,data in (('before',old,before),('after',new,after)):
                    if lines is None:self.assertIsNone(value[side]);continue
                    self.assertEqual(value['hunks'][0][side+'_lines'],lines)
                    self.assertEqual(value['hunks'][0][side+'_line'],start)
                    self.assertEqual(value[side]['changed_line_count'],len(lines))
                    self.assertEqual(value[side]['sha256'],docs.sha(data))
                    self.assertFalse(value[side]['truncated'])
                    self.assertIsNone(value[side]['first_omitted_line'])

    def test_repeated_lines_are_inserted_once(self):
        value=docs.describe({'before':b'a\na\n','after':b'a\na\na\n','path':self.path,'reason':'Repeat'})
        self.assertEqual(value['hunks'],[{'before_line':3,'after_line':3,'before_lines':[],'after_lines':['a']}])
        self.assertEqual(value['before']['changed_line_count'],0)
        self.assertEqual(value['after']['changed_line_count'],1)
        self.assertEqual(value['before']['total_hunks'],0);self.assertEqual(value['after']['total_hunks'],1)

    def test_line_terminator_changes_have_no_invented_line(self):
        before=b'a\nb\nc\n'
        for after in (b'a\r\nb\r\nc\r\n',b'a\nb\nc',b'a\fb\nc\n'):
            with self.subTest(after=after):
                value=docs.describe({'before':before,'after':after,'path':self.path,'reason':'Terminators'})
                self.assertTrue(value['line_terminators_changed']);self.assertEqual(value['hunks'],[])
                self.assertEqual(value['total_hunks'],0)
                for side in ('before','after'):
                    self.assertEqual(value[side]['line_count'],3)
                    self.assertEqual(value[side]['changed_line_count'],0)
                    self.assertIsNone(value[side]['first_omitted_line']);self.assertFalse(value[side]['truncated'])
                    self.assertNotIn('first_changed_line',value[side])
        for old,new in ((before,before),(None,b'')):
            value=docs.describe({'before':old,'after':new,'path':self.path,'reason':'Control'})
            self.assertFalse(value['line_terminators_changed'])

    def test_hunk_truncation_locates_every_omitted_side(self):
        before=('old first\nshared\n'+'old middle\n'*12+'anchor\nold last\n').encode()
        after=('new first\nshared\n'+'new middle\n'*12+'anchor\nnew last\n').encode()
        original=docs.describe({'before':before,'after':after,'path':self.path,'reason':'Partial hunks'})
        self.assertEqual(original['total_hunks'],3)
        def check(value):
            affected=set()
            for side in ('before','after'):
                source=before if side=='before' else after
                expected={h[side+'_line']+i:line for h in original['hunks'] for i,line in enumerate(h[side+'_lines'])}
                shown={h[side+'_line']+i:line for h in value['hunks'] for i,line in enumerate(h[side+'_lines'])}
                self.assertTrue(shown.items()<=expected.items())
                self.assertEqual(sorted(shown),sorted(expected)[:len(shown)])
                missing=expected.keys()-shown.keys();hunks=set()
                for index,hunk in enumerate(original['hunks']):
                    if any(hunk[side+'_line']+i in missing for i in range(len(hunk[side+'_lines']))):hunks.add(index)
                self.assertEqual(value[side]['first_omitted_line'],min(missing) if missing else None)
                self.assertEqual(value[side]['omitted_hunks'],len(hunks))
                self.assertEqual(value[side]['truncated'],bool(missing))
                self.assertEqual(value[side]['sha256'],docs.sha(source))
                self.assertEqual(value[side]['line_count'],len(source.splitlines()))
                self.assertEqual(value[side]['total_hunks'],original[side]['total_hunks'])
                affected |= hunks
            self.assertEqual(value['total_hunks'],3)
            self.assertEqual(value['omitted_hunks'],len(affected))
        # Force both a partial last hunk and complete removal of trailing hunks.
        # Re-fitting the same page must not double-count an already partial hunk.
        result={'changes':[copy.deepcopy(original)]};empty=copy.deepcopy(result)
        empty['changes'][0]['hunks']=[]
        lower=review_pages.wire_size(empty)+100
        partial_seen=False;removed_seen=False
        for budget in range(review_pages.wire_size(result)-1,lower,-40):
            page=copy.deepcopy(result)
            with patch.object(review_pages,'BUDGET',budget):
                try:review_pages.fit(page)
                except service.ServiceError:continue
                check(page['changes'][0]);self.assertLessEqual(review_pages.wire_size(page),budget)
                partial_seen |= any(h.get('before_truncated') or h.get('after_truncated') for h in page['changes'][0]['hunks'])
                removed_seen |= len(page['changes'][0]['hunks'])<3
                saved=copy.deepcopy(page);review_pages.fit(page);self.assertEqual(page,saved)
            page['extra']='Force another fit' * 8
            with patch.object(review_pages,'BUDGET',budget):
                try:review_pages.fit(page)
                except service.ServiceError:continue
                check(page['changes'][0])
        self.assertTrue(partial_seen);self.assertTrue(removed_seen)

    def test_ledger_chunks_obey_encoded_byte_budget(self):
        rows=[{'old_name':str(i),'reason':'quoted " \u2603 '*120} for i in range(32)]
        chunks=list(review_pages.ledger_pages(rows))
        self.assertEqual([r for offset,chunk in chunks for r in chunk],rows)
        self.assertGreater(len(chunks),2)
        for offset,chunk in chunks:
            page={'padding':'x'*4096,'changes':[{'kind':'authored_ledger','row_offset':offset,'added_rows':chunk}]}
            self.assertLessEqual(review_pages.wire_size(page),review_pages.BUDGET)

    def test_ledger_review_refuses_changed_prefix_and_wrong_provenance(self):
        from structured_pass.rename_service import RenameService
        old=self.root/'before';new=self.root/'after';old.mkdir();new.mkdir()
        path='renames.csv';row={'old_name':'Old','new_name':'New','reason':'History','confidence':'high','pass_id':'1'}
        added={**row,'old_name':'Other','new_name':'Better','pass_id':'2'}
        def write(root,rows):
            with (root/path).open('w') as f:
                writer=csv.DictWriter(f,fieldnames=list(row));writer.writeheader();writer.writerows(rows)
        write(old,[row]);write(new,[row,added])
        # Actual review code and CSV reads; assembler views are irrelevant to a ledger-only page.
        fake=SimpleNamespace(ownership=self.ownership,model=lambda g:None,ledger=path,project=self.project,source=self.source,readers=lambda:{},
            state={'generations':{'base':{'checkout':str(old),'manifest':{}},'head':{'checkout':str(new),'manifest':{},
                'base':'base','provenance':[{'kind':'ledger_append','rows':[added]}]}}})
        page=RenameService.review.__wrapped__(fake,'head','base',1)
        self.assertEqual(page['changes'][0]['unchanged_prefix_rows'],1)
        self.assertEqual(page['changes'][0]['added_rows'],[added])
        for rows,code in (([{**row,'reason':'Tampered'},added],'UNCHANGED_LEDGER_REQUIRED'),
                          ([row,{**added,'reason':'Not in provenance'}],'LEDGER_RENAME_MISMATCH')):
            write(new,rows)
            with self.subTest(code=code),self.assertRaisesRegex(ValueError,code):
                RenameService.review.__wrapped__(fake,'head','base',1)

    def test_protected_paths_and_schema(self):
        for path in (self.source,self.project+'project.conf',self.project+'tools/trace/run.py',
                     self.project+'reference/manual.md',self.project+'docs/../project.conf',
                     self.project+'docs/reverse_engineering/../../asm/source.md'):
            with self.subTest(path=path),self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):
                self.prepare([self.op(path=path)])
        for name,code in [('PROGRESS_SCORECARD.md','MIXED_FILE_REQUIRES_TYPED_UPDATE'),
                          ('inventory/unknowns.md','GENERATED_PATH_SERVICE_OWNED')]:
            with self.assertRaisesRegex(ValueError,code):self.prepare([self.op(path=self.project+'docs/reverse_engineering/'+name)])
        for name in ('MEMORY_MAP.md','memory_map.MD','Demo_DX_Systems.md','demo_dx_SYSTEMS.MD'):
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'DOCUMENT_DELETE_CANONICAL_FORBIDDEN'):
                self.prepare([{'kind':'document_delete','path':self.project+'docs/reverse_engineering/'+name,
                               'preimage':'a'*64,'reason':'forbidden'}])
        with self.assertRaisesRegex(ValueError,'DOCUMENT_SCHEMA'):self.prepare([self.op(text=42)])

    def test_review_archives_refuse_creation_modification_and_deletion(self):
        archive=self.project+'docs/reverse_engineering/reviews/pass-59.md'
        target=self.root/archive
        for spelling in (archive,archive.replace('/reviews/','/Reviews/')):
            with self.subTest(action='create',path=spelling),self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):
                self.prepare([self.op(path=spelling,preimage=None,text='Verdict: APPROVED\n')])
        target.parent.mkdir();target.write_text('Existing reviewer judgment\n')
        original=target.read_bytes();self.manifest[archive]=docs.sha(original)
        for spelling in (archive,archive.replace('/reviews/','/Reviews/')):
            for kind in ('document_write','document_delete'):
                op=self.op(path=spelling,kind=kind,preimage=docs.sha(original))
                if kind=='document_delete':del op['text']
                with self.subTest(kind=kind,path=spelling),self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):
                    self.prepare([op])
        self.assertEqual(target.read_bytes(),original)
        self.assertEqual(service.file_ownership(archive,self.project,self.source),'handoff-owned')

    def test_case_folded_ownership_and_inventory_path_policy(self):
        cases={'asm/demo.asm':'source','project.conf':'forbidden','reference/manual.md':'forbidden',
               'mods/test.md':'forbidden','pass_edits.jsonl':'service-owned',
               'docs/reverse_engineering/PROGRESS_SCORECARD.md':'mixed',
               'docs/reverse_engineering/inventory/deferrals.csv':'mixed',
               'docs/reverse_engineering/inventory/raw_ram_review.csv':'mixed',
               'docs/reverse_engineering/reviews/pass-59.md':'handoff-owned'}
        cases.update({name:'generated' for name in service.GENERATED_RELATIVE})
        for relative,owner in cases.items():
            for spelling in (relative,relative.upper(),relative.swapcase()):
                with self.subTest(path=spelling):
                    self.assertEqual(service.file_ownership(self.project+spelling,self.project,self.source),owner)
        (self.root/self.project/'docs/reverse_engineering/inventory').mkdir()
        for directory in ('inventory','Inventory','INVENTORY'):
            op=self.op(path=self.project+'docs/reverse_engineering/'+directory+'/REVIEWER_PROBE.md',preimage=None)
            # Check policy without relying on the host's case sensitivity or the spelling guard.
            with self.subTest(directory=directory),self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):
                docs.selected([op],self.project,self.source,self.ownership)
            with self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):self.prepare([op])

    def test_existing_parent_spelling_and_filename_case_are_exact(self):
        directory=self.root/self.project/'docs/reverse_engineering/Guides';directory.mkdir()
        (directory/'EXISTING.md').write_text('Existing\n')
        for relative in ('docs/reverse_engineering/guides/NEW.md',
                         'docs/reverse_engineering/Guides/existing.md',
                         'Docs/reverse_engineering/Guides/NEW.md'):
            with self.subTest(relative=relative),self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_CASE_MISMATCH'):
                self.prepare([self.op(path=self.project+relative,preimage=None)])
        accepted=self.prepare([self.op(path=self.project+'docs/reverse_engineering/Guides/NEW.md',preimage=None)])
        self.assertIsNone(accepted[0]['before'])

    def test_batch_cannot_introduce_conflicting_directory_spellings(self):
        first=self.op(path=self.project+'docs/reverse_engineering/NewDirectory/A.md',preimage=None)
        second=self.op(path=self.project+'docs/reverse_engineering/newdirectory/B.md',preimage=None)
        with self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_CASE_MISMATCH'):self.prepare([first,second])
        with self.assertRaisesRegex(ValueError,'DOCUMENT_DUPLICATE_OPERATION'):
            self.prepare([first,{**first,'path':first['path'].replace('/A.md','/a.md')}])

    def test_stale_prose_exemption_is_only_the_handoff_archive_directory(self):
        from structured_pass import rename_service
        paths=[self.project+'docs/reverse_engineering/reviews/pass-1.md',
               self.project+'docs/reviews/NOTES.md',
               self.project+'docs/reverse_engineering/notes/reviews/NOTES.md']
        manifest={}
        for path in paths:
            target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('OldName\n')
            manifest[path]=docs.sha(target.read_bytes())
        subject=SimpleNamespace(project=self.project,source=self.source,ownership=self.ownership,
            ledger=self.project+'docs/reverse_engineering/inventory/renames.csv',
            generated={self.project+n for n in service.GENERATED_RELATIVE},
            state={'current':'G','generations':{'G':{'checkout':str(self.root),'manifest':manifest}}},
            model=lambda _:None,manifest_paths=lambda base,ops:list(manifest))
        with patch.object(rename_service,'comments',return_value=[]):
            result=rename_service.RenameService.q09_report(subject,'G',['OldName'])
        self.assertEqual({hit['path'] for hit in result['mentions']},set(paths[1:]))
        with patch.object(rename_service,'ledger_operation',return_value=None),\
             patch.object(rename_service.authored,'selected',return_value=[]),\
             patch.object(rename_service.mixed,'document_operations',return_value=None):
            with self.assertRaisesRegex(ValueError,'UNDISPOSED_STALE_PROSE') as caught:
                rename_service.RenameService.inventory_result(subject,self.root,None,[{'kind':'rename','old_name':'OldName'}])
            self.assertIn(caught.exception.details['paths'][0],paths[1:])

    def test_symlink_and_untracked_file_refuse(self):
        path=self.root/self.path;path.unlink();outside=self.root/'outside';outside.write_text('Before\n');path.symlink_to(outside)
        with self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):self.prepare([self.op()])
        path.unlink();path.write_text('Before\n');self.manifest={}
        with self.assertRaisesRegex(ValueError,'DOCUMENT_PATH_FORBIDDEN'):
            docs.read(self.root,self.manifest,self.path)

    def test_deleted_seed_document_is_removed_before_certification(self):
        # No assembler run: inspect the real validation setup at its certify boundary.
        from unittest.mock import Mock
        state_root=self.root/'state';state_root.mkdir()
        base=self.root/'base';(base/self.source).parent.mkdir(parents=True)
        (base/self.source).write_bytes(b'.END\n')
        reference='projects/demo/reference/demo.nes';(base/reference).parent.mkdir(parents=True)
        (base/reference).write_bytes(b'fixture')
        subject=service.Service.__new__(service.Service)
        subject.root=state_root;subject.source=self.source;subject.reference=reference;subject.cache={}
        subject.fixture={'base_commit':'fixture'}
        subject.state={'current':'G-base','paths':[self.source,self.path],
            'gate_toolchain':{'executables':{'git':'fixture-git'}},'clone_seed':'fixture-seed',
            'generations':{'G-base':{'checkout':str(base),'manifest':{self.source:docs.sha(b'.END\n')}}},
            'candidates':{'C1':{'base':'G-base','status':'draft','revision':0,'attempt':0,
                               'operations':[],'test_only_mutation':False}}}
        subject.save=Mock();subject.candidate=lambda cid:subject.state['candidates'][cid]
        subject.model=lambda generation:SimpleNamespace(source=b'.END\n')
        subject.plan=lambda *args:([],b'.END\n');subject.apply_authored=lambda *args:None
        observed=[]
        def clone(argv,**kwargs):
            checkout=Path(argv[-1]);(checkout/self.path).parent.mkdir(parents=True)
            (checkout/self.path).write_text('Old seed document must stay deleted\n')
            return SimpleNamespace(returncode=0)
        def certify(source,*args,**kwargs):
            observed.append(not (Path(source).parents[3]/self.path).exists())
            raise ValueError('TEST_ONLY_CERTIFICATION_STOP')
        with patch.object(service.subprocess,'run',side_effect=clone),patch.object(service,'git',return_value=''),\
             patch.object(service.gate_environment,'environment',return_value={}),patch.object(service,'certify',side_effect=certify):
            subject._validate('C1')
        self.assertEqual(observed,[True],'DELETED_SEED_DOCUMENT_RESURRECTED')


if __name__=='__main__':unittest.main()
