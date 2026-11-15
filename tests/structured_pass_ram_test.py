"""Lossless RAM evidence and service-owned judgment controls, offline only."""
import copy
import csv
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import artifact_edits as edits, evidence_views, review_pages
from structured_pass import service, producer
from structured_pass.model import digest
from structured_pass.application import apply
from structured_pass.launcher import Corridor
from structured_pass.retained_service import RetainedReviewService
from structured_pass_fixture import prepare, closeout_ops, git, PROJECT


def ledger(rows=None):
    if rows is None:
        rows=[dict(zip(edits.FIELDS['raw_ram_judgments'],
            [key,'candidate','','Existing note','0','yes','3','1','2','1','Entry','Entry']))
            for key in ('0x0040','0x0840','0x6000')]
    stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=edits.FIELDS['raw_ram_judgments'],lineterminator='\r\n')
    writer.writeheader();writer.writerows(rows)
    return stream.getvalue().encode()


def operation(data):
    row=edits.raw_ram_rows(data)[0]
    return {'kind':'raw_ram_judgments','preimage':digest(data),'reason':'Record an unresolved owner contract.',
            'changes':[{'key':row['addr_hex'],'preimage':edits.row_hash(row),
                        'fields':{'status':'deferred','proposed_symbol':'','notes':'Ownership remains unresolved.'}}]}


class JudgmentTests(unittest.TestCase):
    def test_only_authored_fields_change_and_mirrors_remain_distinct(self):
        before=ledger();op=operation(before)
        after=edits.raw_ram_judgments(before,op,'7')
        old,new=edits.raw_ram_rows(before),edits.raw_ram_rows(after)
        self.assertEqual(new[1:],old[1:]);self.assertEqual(new[0]['last_pass_reviewed'],'7')
        self.assertEqual({k:new[0][k] for k in edits.RAW_RAM_GENERATED},
                         {k:old[0][k] for k in edits.RAW_RAM_GENERATED})
        self.assertEqual(after.splitlines(keepends=True)[2:],before.splitlines(keepends=True)[2:])
        self.assertEqual(edits.raw_ram_changes(before,after,judgment_ops=[op],pass_id='7'),[])
        with self.assertRaisesRegex(ValueError,'RAW_RAM_JUDGMENT_CHANGED'):
            edits.raw_ram_changes(before,after)

    def test_refresh_cannot_hide_an_unrequested_judgment(self):
        before=ledger();op=operation(before)
        expected=edits.raw_ram_rows(edits.raw_ram_judgments(before,op,'7'))
        expected[0]['operand_count']='4'
        changes=edits.raw_ram_changes(before,ledger(expected),judgment_ops=[op],pass_id='7')
        self.assertEqual(changes[0]['changed_fields'],['operand_count'])
        expected[1]['notes']='Unrequested judgment'
        with self.assertRaisesRegex(ValueError,'RAW_RAM_JUDGMENT_CHANGED'):
            edits.raw_ram_changes(before,ledger(expected),judgment_ops=[op],pass_id='7')
        with self.assertRaisesRegex(ValueError,'RAW_RAM_JUDGMENT_CHANGED'):
            edits.raw_ram_changes(before,before,judgment_ops=[op],pass_id='7')

    def test_facts_identity_pass_number_schema_and_preimages_are_closed(self):
        data=ledger();base=operation(data)
        for key in (*edits.RAW_RAM_GENERATED,'addr_hex','last_pass_reviewed'):
            op=copy.deepcopy(base);op['changes'][0]['fields'][key]='forged'
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'ARTIFACT_EDIT_SCHEMA'):
                edits.raw_ram_judgments(data,op,'1')
        for mutation,code in [
            (lambda op:op.update(preimage='old'),'ARTIFACT_EDIT_PREIMAGE'),
            (lambda op:op['changes'][0].update(preimage='old'),'ARTIFACT_EDIT_PREIMAGE'),
            (lambda op:op['changes'][0].update(key='0x0041'),'ARTIFACT_ROW_INVALID'),
            (lambda op:op['changes'][0]['fields'].update(status='approved'),'ARTIFACT_ROW_INVALID'),
            (lambda op:op['changes'].append(copy.deepcopy(op['changes'][0])),'ARTIFACT_ROW_DUPLICATE'),
            (lambda op:op['changes'][0].update(row=None),'ARTIFACT_EDIT_SCHEMA')]:
            op=copy.deepcopy(base);mutation(op)
            with self.subTest(code=code),self.assertRaisesRegex(ValueError,code):edits.raw_ram_judgments(data,op,'1')
        for data in (ledger([dict(edits.raw_ram_rows(data)[0],addr_hex='0x2000')]),
                     ledger([dict(edits.raw_ram_rows(data)[0],addr_hex='0X0040')])):
            with self.assertRaisesRegex(ValueError,'ARTIFACT_ROW_INVALID'):edits.raw_ram_rows(data)

    def test_quoted_multiline_and_unmodified_record_bytes_survive(self):
        rows=edits.raw_ram_rows(ledger());rows[1]['notes']='A quoted, note\ncontinued here'
        before=ledger(rows);op=operation(before)
        after=edits.raw_ram_judgments(before,op,'1')
        self.assertEqual(edits.raw_ram_rows(after)[1:],rows[1:])
        self.assertEqual(after.split(b'0x0840',1)[1],before.split(b'0x0840',1)[1])
        # Blank records belong to the surrounding layout, not the edited row.
        spaced=before.replace(b'0x0040',b'\r\n0x0040',1)
        changed=edits.raw_ram_judgments(spaced,operation(spaced),'1')
        self.assertIn(b'\r\n\r\n0x0040',changed)

    def test_authored_fields_refuse_newlines_and_nul(self):
        data=ledger()
        for field in ('status','proposed_symbol','notes'):
            for character in ('\r','\n','\x00'):
                op=operation(data)
                op['changes'][0]['fields'][field]='deferred'+character+'text'
                with self.subTest(field=field,character=repr(character)),self.assertRaisesRegex(ValueError,'^ARTIFACT_EDIT_SCHEMA$'):
                    edits.raw_ram_judgments(data,op,'1')

    def test_writer_does_not_depend_on_compact_read(self):
        with patch.object(evidence_views,'memory',side_effect=ValueError('RESPONSE_TOO_LARGE')):
            self.assertEqual(edits.raw_ram_rows(edits.raw_ram_judgments(ledger(),operation(ledger()),'1'))[0]['status'],'deferred')


class JudgmentLifecycleTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.tmp=tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='ram-test-');self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)

    def test_wrapper_cannot_undo_the_requested_judgment(self):
        data=ledger()
        reset="\nPath('projects/sample/"+edits.RAW_RAM_PATH+"').write_bytes(bytes.fromhex('"+data.hex()+"'))\n"
        c=prepare(self.root,raw_ram=data,gate_extra=reset);g=c.editor.state['current']
        ops=[operation(data),*closeout_ops(c,g)]
        p=c.dispatch('preview',{'generation':g,'operations':ops},'implementer')
        cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
        result=c.dispatch('validate',{'cid':cid},'implementer')
        self.assertNotEqual(result['status'],'validated',result)
        self.assertIn('RAW_RAM_JUDGMENT_CHANGED',json.dumps(result))

    def test_preview_validate_review_restart_and_application(self):
        data=ledger();c=prepare(self.root,raw_ram=data);g=c.editor.state['current'];op=operation(data)
        view=c.dispatch('evidence',{'generation':g,'view':'artifact_rows','artifact':'raw_ram_judgments','key':'0x0040'},'reviewer')
        self.assertEqual(view['preimage'],digest(data));self.assertEqual(view['total_rows'],1)
        self.assertTrue(all(r['row_preimage']==op['changes'][0]['preimage'] for r in view['records']))
        ops=[op,*closeout_ops(c,g)]
        with self.assertRaisesRegex(ValueError,'REVIEWER_MUTATION_DENIED'):
            c.dispatch('preview',{'generation':g,'operations':ops},'reviewer')
        preview=c.dispatch('preview',{'generation':g,'operations':ops},'implementer')
        cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
        result=c.dispatch('validate',{'cid':cid},'implementer');self.assertEqual(result['status'],'validated',result)
        published=c.dispatch('publish',{'cid':cid},'implementer');ticket=published['review']['artifact_id']
        c=Corridor(c.root)
        retained=RetainedReviewService.from_publication(self.root/'retained',c.config['store'],ticket)
        rs=retained.status('reviewer');new=rs['generation']
        # The retained API must include authored changes with the derived pass number.
        record=retained.state['generations'][new];base=record['base'];offset=1;found=[]
        while True:
            page=retained.review(new,base,offset)
            found.extend(page['changes'])
            if page['next_offset'] is None:break
            offset=page['next_offset']
        judgments=[r for r in found if r.get('operation_kind')=='raw_ram_judgments']
        self.assertTrue(judgments,found)
        self.assertTrue(any(r['row']['field']=='last_pass_reviewed' and r['row']['after']=='1' for r in judgments))
        c.dispatch('approve',{'ticket':ticket,'report':'Verdict: APPROVED\n\nSynthetic judgment lifecycle.'},'reviewer')
        c.closeout()
        target=self.root/'target';git(self.root/'repo','clone','-q','--no-hardlinks',str(self.root/'repo'),str(target))
        reference=target/c.editor.reference;reference.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(self.root/'repo'/c.editor.reference,reference)
        git(target,'checkout','-qb','projects');git(target,'config','user.name','Fixture');git(target,'config','user.email','fixture@example.invalid')
        applied=apply(c.root,target,commit=True)
        self.assertEqual(apply(c.root,target,commit=True),applied)
        output=(target/PROJECT/edits.RAW_RAM_PATH).read_bytes()
        self.assertEqual(output,edits.raw_ram_judgments(data,op,'1'))


if __name__=='__main__':unittest.main()
