import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
"""Metadata-only coverage across synthetic publication windows."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from structured_pass.durable_artifact import canonical,digest,SCHEMAS,Store
from structured_pass.publication import ticket_path
from structured_pass import window_coverage as subject

HERE=Path(__file__).resolve().parent


class WindowCoverage(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.states=[]
        for index in range(10):
            body={'schema':SCHEMAS['artifact'],'base_artifact':self.states[-1] if self.states else None,
                  'source_path':'projects/demo/asm/demo.asm','reference_path':'projects/demo/reference/demo.nes',
                  'legacy_generation':'G-'+str(index),'reference_sha256':'b'*64,'producer_sha256':'c'*64,'sequence_fixture':index}
            if index>=8:body['review_anchor']=self.states[7]
            artifact='E-'+digest(canonical(body));self.states.append(artifact)
            path=self.root/'artifacts'/artifact/'receipt.json';path.parent.mkdir(parents=True)
            path.write_bytes(canonical(body))
        for end in (7,8,9):
            items=self.states[:8] if end==7 else self.states[7:end+1]
            ticket={'schema':'published-review-v1' if end==7 else 'published-review-v2',
                    'artifacts':items,'profile':'rename','producer_sha256':'c'*64}
            if end!=7:ticket['anchor_artifact']=self.states[7]
            path=ticket_path(self.root,self.states[end]);path.parent.mkdir(exist_ok=True);path.write_bytes(canonical(ticket))

    def event(self,head,verdict='APPROVED',store=None):
        return {**subject.window(store or self.root,head),'run_id':'fixture-run','reviewer':'fixture-reviewer',
                'round':1,'verdict':verdict,'review_file':'fixture-only-review.md','review_sha256':'d'*64}

    def result(self,events,head=None):
        return subject.coverage(self.root,self.states[0],head or self.states[8],events,
                                run_id='fixture-run',reviewer='fixture-reviewer')

    def test_last_window_alone_does_not_cover_pass(self):
        result=self.result([self.event(self.states[8])])
        self.assertFalse(result['coverage_complete']);self.assertEqual(len(result['uncovered_edges']),7)

    def test_both_windows_and_new_publication(self):
        events=[self.event(self.states[7]),self.event(self.states[8])]
        self.assertTrue(self.result(events)['coverage_complete'])
        self.assertEqual(self.result(events,self.states[9])['uncovered_edges'],[[self.states[8],self.states[9]]])

    def test_negative_verdict_supersedes_earlier_approval(self):
        for verdict in ('CHANGES_REQUESTED','WITHDRAWN'):
            events=[self.event(self.states[7]),self.event(self.states[8]),self.event(self.states[7],verdict)]
            self.assertEqual(len(self.result(events)['uncovered_edges']),7)

    def test_mismatched_window_and_authority_context_refuse(self):
        original=self.event(self.states[7])
        for key,value in [('anchor',self.states[1]),('head',self.states[6]),('edges',original['edges'][1:]),
                          ('ticket_sha256','e'*64),('run_id','other'),('reviewer','other')]:
            event={**original,key:value}
            with self.subTest(key=key),self.assertRaises(ValueError):self.result([event])

    def test_crop_and_wrong_base_refuse(self):
        path=ticket_path(self.root,self.states[8]);ticket=json.loads(path.read_bytes())
        ticket['artifacts']=ticket['artifacts'][1:];path.write_bytes(canonical(ticket))
        with self.assertRaises(ValueError):subject.window(self.root,self.states[8])
        with self.assertRaisesRegex(ValueError,'PASS_BASE_NOT_ANCESTOR'):
            subject.pass_edges(self.root,self.states[9],self.states[8])

if __name__=='__main__':unittest.main(verbosity=2)
