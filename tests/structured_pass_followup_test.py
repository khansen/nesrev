"""Retry and fallback boundaries from the second PR review."""
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import application, paging, producer, review_pages
from structured_pass.launcher import Corridor
from structured_pass.rename_service import comments
from structured_pass_fixture import closeout_ops, git
import structured_pass_readiness_test as readiness
import structured_pass_review_fixes_test as previous


class DiagnosticFallbackTests(unittest.TestCase):
    diagnostic=readiness.ReadinessTests.diagnostic

    def test_scalar_fallback_sanitizes_keys_and_values(self):
        key='/private/checkouts/project/projects/sample/asm/sample.asm:2: LDA #Cell'
        payload={key:'See /secret/private/file.txt',
                 'large_nested_report':['quote " \\ '*200 for _ in range(70)]}
        result=self.diagnostic(json.dumps(payload)+'\n',max_output=4096)
        self.assertIn('detail_notice',result)  # Prove that the scalar fallback ran.
        self.assertTrue(result['report'])
        wire=json.dumps(result)
        for secret in ('LDA #Cell','/private/checkouts/project','/secret/private'):
            self.assertNotIn(secret,wire)
        self.assertIn('source text omitted',wire)
        self.assertLessEqual(review_pages.wire_size(result),4096)


class PreviewWireTests(unittest.TestCase):
    def test_quote_heavy_records_split_by_encoded_wire_size(self):
        records=[{'kind':'comment_replace','record_id':str(i),'text':'; '+('"\\'*1200)} for i in range(7)]
        offset=0;seen=[];pages=[]
        while offset is not None:
            page=paging.page(records,offset,40);pages.append(page)
            payload={'generation':'G-'+'0'*20,'candidate':None,'revision':None,
                     'preview_digest':'f'*64,'summary':{'renames':0,'comments':7,'documents':0},**page}
            self.assertLessEqual(review_pages.wire_size(payload),paging.MAX_BYTES)
            seen.extend(page['records']);offset=page['next_offset']
        self.assertEqual(seen,records);self.assertGreater(len(pages),1)


class CloseoutAndPreviewTests(unittest.TestCase):
    setUp=previous.ReviewWorkflowTests.setUp
    edit=previous.ReviewWorkflowTests.edit
    bridge=previous.ReviewWorkflowTests.bridge
    approved_target=previous.ReviewWorkflowTests.approved_target

    def reapprove(self,ticket):
        c=self.c
        c.dispatch('request-changes',{'ticket':ticket,'report':'Verdict: CHANGES_REQUESTED\nClarify the report.'},'reviewer')
        c.dispatch('reready',{'response':'Reviewed clarification; no source edit required.'},'implementer')
        c.dispatch('approve',{'ticket':ticket,'report':'Verdict: APPROVED\nClarification accepted.'},'reviewer')

    def test_unapplied_archive_is_preserved_across_reapproval_and_application(self):
        p,target=self.approved_target();c=self.c
        first=c.dispatch('closeout',{},'implementer')
        canonical=c.root/'handoff'/first['archive'];original=canonical.read_bytes()
        self.reapprove(p['review']['artifact_id'])
        second=self.bridge('closeout',{})
        self.assertNotEqual(first['archive_sha256'],second['archive_sha256'])
        self.assertEqual((c.root/'handoff'/first['archive_snapshot']).read_bytes(),original)
        self.assertEqual((c.root/'handoff'/second['archive_snapshot']).read_bytes(),canonical.read_bytes())
        self.assertEqual(producer.sha(canonical),second['archive_sha256'])
        result=application.apply(c.root,target,commit=True)
        self.assertEqual(result['status'],'committed')
        self.assertEqual((target/second['archive']).read_bytes(),canonical.read_bytes())
        self.assertEqual(application.apply(c.root,target,commit=True),result)
        self.reapprove(p['review']['artifact_id'])
        before=canonical.read_bytes();head=git(target,'rev-parse','HEAD')
        with self.assertRaisesRegex(ValueError,'^CLOSEOUT_ALREADY_APPLIED$'):
            application.apply(c.root,target,commit=True)
        self.assertEqual(canonical.read_bytes(),before)
        self.assertEqual(git(target,'rev-parse','HEAD'),head)
        canonical.unlink()
        with self.assertRaisesRegex(ValueError,'^CLOSEOUT_ALREADY_APPLIED$'):
            application.apply(c.root,target,commit=True)
        self.assertFalse(canonical.exists())
        self.assertEqual(git(target,'rev-parse','HEAD'),head)

    def test_archive_creation_is_inside_the_application_approval_lock(self):
        p,target=self.approved_target();c=self.c;original=Corridor._closeout
        state=c.root/'handoff/.agents/current.json';before=state.read_bytes()
        report=c.root/'handoff/revoke.md';report.write_text('Verdict: CHANGES_REQUESTED\nMust repair.')
        attempts=[]
        def revoke(controller,*args):
            closed=original(controller,*args)
            result=subprocess.run([sys.executable,'-B',str(ROOT/'scripts/agent_review.py'),
                '--repo',str(c.root/'handoff'),'--expected-run-id',c.config['run_id'],
                'request-changes','--window',p['review']['artifact_id'],'--review',str(report)],
                capture_output=True,text=True)
            attempts.append(result)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('REVIEW_STATE_BUSY',result.stderr)
            self.assertEqual(state.read_bytes(),before)
            return closed
        with patch.object(Corridor,'_closeout',revoke):
            result=application.apply(c.root,target,commit=True)
        self.assertEqual(len(attempts),1);self.assertEqual(result['status'],'committed')

    def test_archive_retry_after_interrupted_receipt_and_tamper_refusal(self):
        p,_=self.approved_target();c=self.c
        first=c.dispatch('closeout',{},'implementer')
        (c.root/'closed.json').unlink()  # Archive is durable before this receipt.
        self.assertEqual(c.dispatch('closeout',{},'implementer'),first)
        self.reapprove(p['review']['artifact_id'])
        archive=c.root/'handoff'/first['archive'];archive.write_bytes(b'Unrecognized archive')
        before=archive.read_bytes()
        with self.assertRaisesRegex(ValueError,'^REVIEW_ARCHIVE_EXISTS$'):
            c.dispatch('closeout',{},'implementer')
        self.assertEqual(archive.read_bytes(),before)

    def test_quote_heavy_preview_returns_digest_and_refuses_oversize_before_registration(self):
        c=self.c;g=c.editor.state['current'];comment=comments(c.editor.model(g))[0]
        def operations(repeats):
            return [{'kind':'comment_replace','record_id':comment['record_id'],
                'preimage':comment['preimage_sha256'],'text':'; '+('"\\'*repeats),
                'reason':'Exercise MCP escaping'},*closeout_ops(c,g)]
        first=self.bridge('preview',{'generation':g,'operations':operations(2000)})
        self.assertIn('preview_digest',first)
        rows=list(first['records']);offset=first['next_offset']
        while offset is not None:
            page=self.bridge('preview_page',{'generation':g,'preview_digest':first['preview_digest'],'offset':offset})
            rows.extend(page['records']);offset=page['next_offset']
        self.assertEqual(len(rows),first['total_records'])
        self.assertEqual(sum(row.get('kind')=='comment_replace' for row in rows),1)
        before=c.editor.state_path.read_bytes()
        paths={p.name:p.read_bytes() for p in (c.editor.root/'previews').iterdir()}
        with self.assertRaisesRegex(ValueError,'^PREVIEW_ITEM_TOO_LARGE$'):
            c.dispatch('preview',{'generation':g,'operations':operations(4000)},'implementer')
        self.assertEqual(c.editor.state_path.read_bytes(),before)
        self.assertEqual({p.name:p.read_bytes() for p in (c.editor.root/'previews').iterdir()},paths)
        confirmed=self.bridge('confirm',{'generation':g,'preview_digest':first['preview_digest']})
        self.assertEqual(confirmed['confirmed_preview_digest'],first['preview_digest'])


if __name__=='__main__':unittest.main()
