import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
"""Neutral document fixtures for protected scorecard and deferral mutations."""
import copy
import unittest

from structured_pass import mixed_documents as mixed


SCORECARD=b'''# Progress

| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | raw_ptr_immediates_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | prior corridor | 0 / 0 | 0 | 0 | 0 | not measured | not measured | pass | pass | 2 | Previous result. |
'''
DEFERRALS=(','.join(mixed.DEFERRAL_FIELDS)+'\n').encode()


def operations(scorecard=SCORECARD,deferrals=DEFERRALS):
    return [
        {'kind':'scorecard_update','pass_id':'2','preimage':mixed.sha(scorecard),
         'fields':{'focus':'fixture corridor','notes':'Fixture input.'}},
        {'kind':'closeout','pass_id':'2','deferrals_preimage':mixed.sha(deferrals),'rework_items':0,
         'deferrals':[{'subject':'fixture gap','revisit_condition':'independent evidence','kind':'static'}]}]


class MixedDocuments(unittest.TestCase):
    def test_new_row_cannot_seed_wrapper_results(self):
        for key,value in [('verify','pass'),('docs_check','pass'),('rework_items','0'),('pass_id','1')]:
            ops=operations();ops[0]['fields'][key]=value
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'^WRAPPER_OWNED_FIELD$'):
                mixed.prepare(SCORECARD,DEFERRALS,ops,'2')

    def test_existing_row_cannot_override_results(self):
        for key in mixed.PROTECTED:
            ops=operations();ops[0]['pass_id']=ops[1]['pass_id']='1';ops[0]['fields']={key:'pass'}
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'^WRAPPER_OWNED_FIELD$'):
                mixed.prepare(SCORECARD,DEFERRALS,ops,'1')

    def test_new_row_is_pending_and_prior_row_is_unchanged(self):
        result=mixed.prepare(SCORECARD,DEFERRALS,operations(),'2')
        parsed=mixed.Scorecard(result['data'])
        self.assertEqual(parsed.rows['1'],mixed.Scorecard(SCORECARD).rows['1'])
        self.assertTrue(all(parsed.rows['2'][key]=='pending' for key in mixed.GATE_FIELDS|mixed.SYNCED_FIELDS))
        self.assertTrue(all(parsed.rows['2'][key]==mixed.UNMEASURED for key in mixed.UNMEASURED_FIELDS))
        self.assertEqual(result['deferrals_before'],[])
        self.assertEqual(result['deferrals_expected'][0]['subject'],'fixture gap')

    def test_historical_retro_row_is_preserved(self):
        data=SCORECARD+SCORECARD.splitlines()[-1].replace(b'| 1 |',b'| retro-0 |')+b'\n'
        result=mixed.prepare(data,DEFERRALS,operations(scorecard=data),'2')
        self.assertEqual(mixed.Scorecard(result['data']).rows['retro-0'],mixed.Scorecard(data).rows['retro-0'])

    def test_changed_draft_does_not_reuse_green_cells(self):
        ops=operations();ops[0]['pass_id']=ops[1]['pass_id']='1';ops[0]['fields']={'notes':'Rechecked input.'}
        changed=mixed.Scorecard(mixed.prepare(SCORECARD,DEFERRALS,ops,'1')['data']).rows['1']
        self.assertEqual(changed['focus'],'prior corridor')
        self.assertTrue(all(changed[key]=='pending' for key in mixed.GATE_FIELDS|mixed.SYNCED_FIELDS))
        self.assertTrue(all(changed[key]==mixed.UNMEASURED for key in mixed.UNMEASURED_FIELDS))

    def test_every_measured_column_is_wrapper_owned(self):
        for key in mixed.SYNCED_FIELDS|mixed.UNMEASURED_FIELDS:
            for pass_id in ('1','2'):
                ops=operations();ops[0]['pass_id']=ops[1]['pass_id']=pass_id
                ops[0]['fields'][key]='-12 (warnings retired)' if key=='warnings_baseline_delta' else '0'
                with self.subTest(key=key,pass_id=pass_id),self.assertRaisesRegex(ValueError,'^WRAPPER_OWNED_FIELD$'):
                    mixed.prepare(SCORECARD,DEFERRALS,ops,pass_id)

    def test_preimage_pass_and_closeout_binding(self):
        for index,key,value,error in [(0,'preimage','changed','MIXED_DOCUMENT_PREIMAGE'),
                                      (1,'deferrals_preimage','changed','MIXED_DOCUMENT_PREIMAGE'),
                                      (1,'pass_id','3','DOCUMENT_PASS_MISMATCH')]:
            ops=operations();ops[index][key]=value
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'^'+error+'$'):
                mixed.prepare(SCORECARD,DEFERRALS,ops,'2')
        with self.assertRaisesRegex(ValueError,'^CLOSEOUT_REQUIRED$'):
            mixed.prepare(SCORECARD,DEFERRALS,operations()[:1],'2')
        with self.assertRaisesRegex(ValueError,'^DOCUMENT_PASS_MISMATCH$'):
            mixed.prepare(SCORECARD,DEFERRALS,operations(),'3')

    def test_wrapper_request_cannot_supply_results_or_commands(self):
        for key in ['verify','docs_check','command','environment','script_dir']:
            ops=operations();ops[1][key]='forged'
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'^MIXED_DOCUMENT_SCHEMA$'):
                mixed.prepare(SCORECARD,DEFERRALS,ops,'2')

    def test_closeout_rows_are_append_only_and_conflicts_refuse(self):
        data=DEFERRALS+b'2,fixture corridor,fixture gap,static,fixture gap,independent evidence,open\n'
        ops=operations(deferrals=data)
        self.assertEqual(mixed.prepare(SCORECARD,data,ops,'2')['deferrals_expected'],mixed.deferral_rows(data))
        for key,value in [('revisit_condition','different'),('kind','runtime')]:
            bad=copy.deepcopy(ops);bad[1]['deferrals'][0][key]=value
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'^DEFERRAL_ROW_CONFLICT$'):
                mixed.prepare(SCORECARD,data,bad,'2')

    def test_identical_repeated_header_and_new_row(self):
        lines=SCORECARD.splitlines(keepends=True)
        header=next(i for i,line in enumerate(lines) if line.startswith(b'| pass_id'))
        repeated=SCORECARD+b'\n## Continuation\n\n'+b''.join(lines[header:header+2])+lines[-1].replace(b'| 1 |',b'| 2 |')
        parsed=mixed.Scorecard(repeated)
        data,_,_=parsed.update('3',{'focus':'New corridor','notes':'New finding.'})
        after=mixed.Scorecard(data)
        self.assertEqual(set(after.rows),{'1','2','3'})
        for pid in ('1','2'):self.assertEqual(after.rows[pid],parsed.rows[pid])
        tail=b''.join(lines[header:header+2]).replace(b'| focus |',b'| notes |').replace(b'| notes |\n',b'| focus |\n')
        with self.assertRaisesRegex(ValueError,'MIXED_DOCUMENT_SCHEMA'):
            mixed.Scorecard(SCORECARD+tail)

    def test_ambiguous_headers_rows_and_payloads_refuse(self):
        for data in [SCORECARD+SCORECARD,SCORECARD.replace(b'| 1 |',b'| 01 |'),
                     SCORECARD.replace(b'| notes |',b'| notes | notes |')]:
            with self.subTest(data=data),self.assertRaisesRegex(ValueError,'^MIXED_DOCUMENT_SCHEMA$'):
                mixed.Scorecard(data)
        for value in ['text | forged','text\0row']+['text'+c+'row' for c in '\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029']:
            ops=operations();ops[0]['fields']['notes']=value
            with self.subTest(value=value),self.assertRaisesRegex(ValueError,'^MIXED_DOCUMENT_SCHEMA$'):
                mixed.prepare(SCORECARD,DEFERRALS,ops,'2')


if __name__=='__main__':unittest.main(verbosity=2)
