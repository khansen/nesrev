import sys,base64
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
"""Neutral fixtures for the durable envelope, identity split and tamper errors."""
import copy
import gzip
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from structured_pass.durable_artifact import Store, canonical, content_id, digest, tooling_id, running_tooling, FACT_READERS


class ArtifactTest(unittest.TestCase):
    def setUp(self):
        self.temporary=tempfile.TemporaryDirectory(prefix='nesrev-artifact-test-')
        self.root=Path(self.temporary.name);self.store=Store(self.root/'retained')
        self.checkout=self.root/'checkout';self.checkout.mkdir()
        self.capture=self.root/'capture';self.capture.mkdir()
        self.source=b'.ORG $8000\nEntry:\nNOP\n.END\n'
        # No original asm file exists: units alone must carry it.
        (self.capture/'model.json').write_bytes(canonical({'files':[{'id':'f1','bytes_base64':base64.b64encode(self.source).decode(),'byte_length':len(self.source),'sha256':digest(self.source)}], 'units':[{'id':'u1','file_id':'f1','byte_start':0,'byte_end_exclusive':len(self.source)}]}))
        (self.capture/'stable-ids.json').write_bytes(b'{"1":"record-1"}\n')
        (self.checkout/'ledger.csv').write_bytes(b'old,new\n')
        (self.checkout/'guide.md').write_bytes(b'# Fixture\n')
        (self.checkout/'reference.bin').write_bytes(b'fixture reference')
        self.reader=self.root/'readers';self.reader.mkdir()
        self.reader_paths={name:self.reader/name for name in FACT_READERS}
        for path in self.reader_paths.values():
            path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'# reader one\n')
        self.service=self.reader/'service.py';self.service.write_bytes(b'# lifecycle one\n')
        self.binary=self.root/'producer';self.binary.write_bytes(b'fixture producer')
        (self.root/'source.tar.gz').write_bytes(b'fixture source archive');(self.root/'local.patch').write_bytes(b'')
        self.recipe=self.root/'recipe.json';self.recipe.write_bytes(canonical({
            'source_archive_sha256':digest(b'fixture source archive'),'local_diff_sha256':digest(b'')}))
        self.manifest={'source.asm':digest(self.source),'ledger.csv':digest((self.checkout/'ledger.csv').read_bytes()),
                       'guide.md':digest((self.checkout/'guide.md').read_bytes())}
        self.state={'producer_sha256':digest(self.binary.read_bytes()),
            'reader_hashes':{name:digest(path.read_bytes()) for name,path in {**self.reader_paths,'service.py':self.service}.items()},
            'reference_sha256':digest((self.checkout/'reference.bin').read_bytes()),
            'generations':{'legacy':{'manifest':self.manifest,'checkout':str(self.checkout),
                'capture':str(self.capture),'capture_hashes':{f.name:digest(f.read_bytes()) for f in self.capture.iterdir()},
                'base':None}}}
        self.exported=self.export(self.state,'legacy')

    def tearDown(self):self.temporary.cleanup()

    def export(self,state,generation,base=None):
        return self.store.export(state,generation,'source.asm','reference.bin',[self.reader],self.binary,self.recipe,base)

    def runtime(self):return running_tooling(self.binary,self.reader_paths)

    def body(self):return self.store.open(self.exported['artifact_id'],self.runtime())

    def tamper_blob(self,sha,data):self.store.blob_path(sha).write_bytes(gzip.compress(data,mtime=0))

    def test_all_manifest_paths_and_source_survive_original_deletion(self):
        shutil.rmtree(self.checkout);shutil.rmtree(self.capture)
        destination=self.root/'restored';body=self.store.materialize(self.exported['artifact_id'],self.runtime(),destination)
        self.assertEqual((destination/'project/source.asm').read_bytes(),self.source)
        for path,sha in self.manifest.items():self.assertEqual(digest((destination/'project'/path).read_bytes()),sha)
        self.assertEqual(body['manifest'],self.manifest)

    def test_tooling_change_does_not_rekey_content(self):
        self.reader_paths['model.py'].write_bytes(b'# changed reader\n');new=copy.deepcopy(self.state)
        new['reader_hashes']['model.py']=digest(self.reader_paths['model.py'].read_bytes())
        changed=self.export(new,'legacy')
        self.assertEqual(changed['content_id'],self.exported['content_id'])
        self.assertNotEqual(changed['tooling_id'],self.exported['tooling_id'])
        with self.assertRaisesRegex(ValueError,'^TOOLING_IDENTITY_MISMATCH$'):
            self.store.open(self.exported['artifact_id'],self.runtime())

    def test_lifecycle_change_does_not_rekey_facts(self):
        self.service.write_bytes(b'# lifecycle two\n');state=copy.deepcopy(self.state)
        state['reader_hashes']['service.py']=digest(self.service.read_bytes())
        changed=self.export(state,'legacy')
        self.assertEqual(changed['content_id'],self.exported['content_id'])
        self.assertEqual(changed['tooling_id'],self.exported['tooling_id'])
        self.body()

    def test_unit_byte_tamper(self):
        body=self.body();self.tamper_blob(body['captures']['model.json'],canonical({'hex':(b'X'+self.source[1:]).hex()}))
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_UNIT_MISMATCH$'):self.body()

    def test_ledger_tamper(self):
        self.tamper_blob(self.manifest['ledger.csv'],b'old,new\nwrong,row\n')
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_FILE_MISMATCH$'):self.body()

    def test_provenance_tamper(self):
        body=self.body();self.tamper_blob(body['provenance'],b'[{"forged":true}]')
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_PROVENANCE_MISMATCH$'):self.body()

    def test_manifest_tamper(self):
        path=Path(self.exported['receipt']);body=json.loads(path.read_bytes())
        body['manifest']['ledger.csv']='0'*64;path.write_bytes(canonical(body))
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_MANIFEST_MISMATCH$'):self.body()

    def test_swapped_base(self):
        state=copy.deepcopy(self.state);state['generations']['changed']=copy.deepcopy(state['generations']['legacy'])
        state['generations']['changed'].update(base='legacy',provenance=[{'kind':'fixture'}])
        changed=self.export(state,'changed',self.exported['artifact_id'])
        with self.assertRaisesRegex(ValueError,'^BASE_ARTIFACT_MISMATCH$'):
            self.store.open(changed['artifact_id'],self.runtime(),'E-'+'0'*64)

    def test_changed_reference_changes_content(self):
        self.assertNotEqual(content_id(self.manifest,self.state['reference_sha256']),content_id(self.manifest,'0'*64))

    def test_path_traversal_refused(self):
        state=copy.deepcopy(self.state);state['generations']['legacy']['manifest']['../outside']='0'*64
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_PATH_INVALID$'):self.export(state,'legacy')


if __name__=='__main__':unittest.main()
