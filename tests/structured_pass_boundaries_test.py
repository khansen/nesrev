"""Boundary, transaction and ownership controls without producer runs."""
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

    def prepare(self,ops):return docs.prepare(self.root,self.manifest,ops,self.project,self.source,service.file_ownership)

    def test_existing_new_deleted_documents_and_preimages(self):
        result=self.prepare([self.op()]);self.assertEqual(result[0]['before'],b'Before\n')
        self.assertEqual(result[0]['after'],b'After\n')
        new=self.op(path=self.project+'docs/reverse_engineering/OPTIONAL.md',preimage=None)
        self.assertIsNone(self.prepare([new])[0]['before'])
        delete={k:v for k,v in self.op(kind='document_delete').items() if k!='text'}
        self.assertIsNone(self.prepare([delete])[0]['after'])
        with self.assertRaisesRegex(ValueError,'DOCUMENT_PREIMAGE_MISMATCH'):self.prepare([self.op(preimage=None)])

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
                docs.selected([op],self.project,self.source,service.file_ownership)
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
        subject=SimpleNamespace(project=self.project,source=self.source,
            ledger=self.project+'docs/reverse_engineering/inventory/renames.csv',
            generated={self.project+n for n in service.GENERATED_RELATIVE},
            state={'current':'G','generations':{'G':{'checkout':str(self.root),'manifest':manifest}}},
            model=lambda _:None,manifest_paths=lambda base,ops:list(manifest))
        with patch.object(rename_service,'comments',return_value=[]):
            result=rename_service.RenameService.q09.__wrapped__(subject,'G',['OldName'])
        self.assertEqual({hit['path'] for hit in result['mentions']},set(paths[1:]))
        with patch.object(rename_service,'ledger_operation',return_value=None),\
             patch.object(rename_service.authored,'selected',return_value=[]),\
             patch.object(rename_service.mixed,'document_operations',return_value=None):
            with self.assertRaisesRegex(ValueError,'UNDISPOSED_STALE_PROSE'):
                rename_service.RenameService.inventory_result(subject,self.root,None,[{'kind':'rename','old_name':'OldName'}])

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
