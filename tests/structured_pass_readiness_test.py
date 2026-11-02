"""Bounded diagnostics and compact view controls; no provider inference."""
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import gate_diagnostics,rename_service,review_pages


class ReadinessTests(unittest.TestCase):
    def test_use_groups_obey_byte_limit_and_preserve_every_reference(self):
        refs=['r'+str(i) for i in range(30)];op={'declaration_id':'d','reference_ids':refs}
        model=SimpleNamespace()
        with patch.object(rename_service,'use_view',side_effect=lambda a,b,r,d:{'reference_id':r,'record':'quoted " \u2603 '*180}):
            pages=rename_service.use_pages(None,model,op,'base')
            self.assertEqual([r for page in pages for r in page],refs)
            self.assertTrue(all(len(page)<=8 for page in pages))
            self.assertGreater(len(pages),4)
            for page in pages:
                rows=[rename_service.use_view(None,model,r,'d') for r in page]
                self.assertLessEqual(review_pages.wire_size({'changes':rows}),review_pages.BUDGET-4096)
            with patch.object(rename_service,'use_view',side_effect=AssertionError('Unexpected recomputation')):
                self.assertEqual(rename_service.use_pages(None,model,op,'base'),pages)
        with patch.object(rename_service,'use_view',side_effect=lambda a,b,r,d:{'reference_id':r}):
            pages=rename_service.use_pages(None,SimpleNamespace(),op,'base')
            self.assertEqual([len(page) for page in pages],[8,8,8,6])

    def diagnostic(self,text,**kwargs):
        with tempfile.TemporaryDirectory() as temporary:
            log=Path(temporary)/'gate.log';log.write_text(text)
            model=SimpleNamespace(source=b'Cell .EQU 16\nLDA #Cell\nRTS\n',facts={})
            return gate_diagnostics.explanation(log,'/private/checkouts/project','projects/sample/asm/sample.asm',model,**kwargs)

    def test_failure_lines_survive_json_and_remove_host_paths_and_source(self):
        result=self.diagnostic('FAIL: /private/checkouts/project/projects/sample/docs/note.md: missing condition\nPORTS_MISSING\n'
            'ERROR: /secret/location.txt unavailable\nFAIL: projects/sample/asm/sample.asm:2: LDA #Cell\n'
            '{"summary":"No stale old-symbol references found","residue":[]}\n')
        self.assertEqual(result['failure_line_count_in_tail'],3)
        self.assertEqual(len(result['failure_lines']),3)
        self.assertIn('missing condition',result['failure_lines'][0])
        self.assertIn('projects/sample/docs/note.md',result['failure_lines'][0])
        self.assertEqual(result['report']['residue'],[])
        self.assertTrue(result['failure_context'])
        self.assertEqual(result['failure_context'][0],{'failure_index':0,'lines':['PORTS_MISSING']})
        encoded=json.dumps(result)
        for private in ('/private/checkouts','/secret','LDA #Cell'):self.assertNotIn(private,encoded)
        self.assertIn('[source text omitted',encoded)

    def test_diagnostics_fit_wire_budget_with_failure_priority(self):
        text=''.join('FAIL: problem '+str(i)+' '+('"\u2603'*900)+'\n' for i in range(100))
        text+=json.dumps({'summary':'Summary that does not override failure','residue':[{'text':'x'*500}]*90})+'\n'
        result=self.diagnostic(text,max_output=3072)
        self.assertLessEqual(review_pages.wire_size(result),3072)
        self.assertTrue(result['truncated']);self.assertTrue(result['failure_lines_truncated'])
        self.assertTrue(result['failure_lines']);self.assertIn('FAIL:',result['failure_lines'][0])
        self.assertTrue(result['log_tail_truncated'])

    def test_residue_json_and_plain_text_still_available(self):
        residue={'summary':'Stale prose','residue':[{'symbol':'OldName','file':'projects/sample/docs/note.md','line':7,'text':'OldName'}]}
        result=self.diagnostic(json.dumps(residue)+'\n')
        self.assertEqual(result['report'],residue);self.assertEqual(result['failure_lines'],[])
        result=self.diagnostic('ordinary output\nFAIL: missing evidence\n')
        self.assertEqual(result['format'],'text');self.assertIn('ordinary output',result['lines'])
        self.assertEqual(result['failure_lines'],['FAIL: missing evidence'])


if __name__=='__main__':unittest.main()
