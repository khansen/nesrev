"""Visible byte accounting must include escaping, envelopes and refusals."""
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import bridge, operation_contract, paging


class VolumeTests(unittest.TestCase):
    def emit(self,answer,*,identifier=123,error=False):
        output=io.StringIO()
        response={'result':{'content':[{'type':'text','text':json.dumps(answer)}]}}
        if error:response['result']['isError']=True
        bridge.emit(None,identifier,response,output,'search')
        wire=output.getvalue();decoded=json.loads(wire)
        value=json.loads(decoded['result']['content'][0]['text'])
        self.assertEqual(value['volume']['response_bytes'],len(wire.encode()))
        self.assertEqual(value['volume']['question_limit_bytes'],409600)
        return wire,decoded,value

    def test_exact_wire_bytes_for_unicode_escaping_and_error(self):
        for identifier in (1,'a-long-request-identifier',None):
            for error in (False,True):
                with self.subTest(identifier=identifier,error=error):
                    self.emit({'text':'\\"\n🦆'*100,'error':'SEARCH_SCHEMA'} if error
                              else {'rows':[{'text':'\\"\n🦆'*100}]},
                              identifier=identifier,error=error)

    def test_accounting_cannot_borrow_space_from_response_cap(self):
        wire,decoded,value=self.emit({'rows':['x'*paging.MAX_BYTES]})
        self.assertLessEqual(len(wire.encode()),paging.MAX_BYTES)
        self.assertTrue(decoded['result']['isError'])
        self.assertEqual(value['error'],'RESPONSE_TOO_LARGE')
        self.assertNotIn('rows',value)

    def test_reference_budget_is_bounded_and_explicit(self):
        self.assertEqual(operation_contract.QUESTION_BYTES,400*1024)
        text=operation_contract.REQUEST_COUNTING
        for required in ('409600 bytes','24576-byte maximum','context before=0, after=0',
                         'lower bound','Narrow','stop for a decision','edits, validation',
                         'not a fresh allowance'):
            self.assertIn(required,text)


if __name__=='__main__':unittest.main()
