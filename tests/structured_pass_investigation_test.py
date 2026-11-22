"""Coverage is service evidence, never a model's completion assertion."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import structured_pass_evidence_test as fixture
import structured_pass_codex_client_test as native_fixture
import structured_codex_client as client
from structured_pass import corridor_inventory, corridor_capacity, navigation, investigation as inv


class InvestigationTests(unittest.TestCase):
    def setUp(self):
        fixture.EvidenceTests.setUp(self)
        spec = {'roots': [{'symbol': 'Entry', 'through_return': 'RTS'}],
                'vector': 'Pointers', 'ram_ranges': [[0, 2047]], 'analogues': []}
        self.inventory = corridor_inventory.build(self.model, spec)
        self.catalog = inv.catalog(self.model, 'G-frozen', self.inventory)
        plan = inv.partition_plan(self.catalog, [{'id': 'all', 'sets': list(self.catalog['sets'])}])
        self.entry = plan['entries'][0]
        self.audit = {'session_id': 'fresh-thread', 'last_compaction': -1,
                      'deliveries': [{'call_id': 'read', 'response_sha256': 'page-hash', 'position': 3}]}
        self.receipts = [inv.receipt(self.catalog, 'fresh-thread', 'read', self.entry['units'], 'page-hash')]

    def submission(self, absence=False):
        key = next(iter(self.catalog['evidence']))
        return {'claims': [{'id': 'claim-1', 'kind': 'absence' if absence else 'positive',
                 'statement': 'Synthetic bounded claim, subject to semantic review.', 'confidence': 'inferred',
                 'citations': [{'id': key, 'sha256': self.catalog['evidence'][key]['content_sha256']}],
                 'searched_sets': list(self.catalog['sets']) if absence else [],
                 'unknowns': 'Indirect destinations remain unknown.', 'contrary': []}],
                'decisions': [{'statement': 'Keep the uncertain name unchanged.', 'claims': ['claim-1']}]}

    def save(self, submission=None, receipts=None, audit=None):
        return inv.checkpoint(self.catalog, self.entry, submission or self.submission(),
                              self.receipts if receipts is None else receipts,
                              self.audit if audit is None else audit, maximum_bytes=65536)

    def test_parent_fact_ids_keep_full_membership_and_partition_union(self):
        actual = inv.catalog(self.model, 'G-frozen', self.inventory)
        self.assertEqual(actual, self.catalog)
        shared = [r for r in actual['evidence'].values() if r['kind'] == 'ram' and len(r['fact']['addresses']) > 1]
        self.assertTrue(shared)
        ram_sets = [s for s in actual['sets'] if s.startswith('ram:')]
        other_sets = sorted(set(actual['sets']) - set(ram_sets))
        entries = [{'id': 'source', 'sets': other_sets}] + [
            {'id': 'byte-' + str(i), 'sets': [s]} for i, s in enumerate(ram_sets)]
        plan = inv.partition_plan(actual, entries)
        self.assertEqual({u for e in plan['entries'] for u in e['units']}, set(actual['units']))
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_COVERAGE_INCOMPLETE$'):
            inv.partition_plan(actual, entries[:-1])
        changed = inv.catalog(self.model, 'G-other', self.inventory)
        self.assertNotEqual(set(changed['evidence']), set(actual['evidence']))
        row = next(r['fact'] for r in shared if r['fact']['category'] == 'unresolved_indirect_destination')
        for field, value in [('addresses', row['addresses'][:1]), ('exact_destination', True)]:
            altered = {**row, field: value}
            self.assertNotEqual(inv.identity(altered), inv.identity(row))

    def test_complete_checkpoint_and_consumer_recheck(self):
        saved = self.save(self.submission(absence=True))
        self.assertEqual(saved['completion'], 'complete')
        view = inv.handoff(saved, self.catalog)
        self.assertNotIn('completed', view['coverage'])
        self.assertEqual(view['coverage']['completed_count'], len(self.entry['units']))
        self.assertTrue(view['sources'])
        receipt = inv.recheck(saved, self.catalog, self.entry, self.receipts, self.audit, maximum_bytes=65536)
        self.assertEqual(receipt['checkpoint_sha256'], saved['sha256'])
        later = {**self.audit, 'deliveries': self.audit['deliveries'] + [
            {'call_id': 'later-status', 'response_sha256': 'status', 'position': 4}]}
        self.assertEqual(inv.recheck(saved, self.catalog, self.entry, self.receipts, later,
                                    maximum_bytes=65536)['checkpoint_sha256'], saved['sha256'])
        changed = inv.catalog(self.model, 'G-other', self.inventory)
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_'):
            inv.recheck(saved, changed, self.entry, self.receipts, self.audit, maximum_bytes=65536)

    def test_compaction_voids_preceding_reads_even_if_checkpoint_was_accepted(self):
        saved = self.save(self.submission(absence=True))
        compacted = {**self.audit, 'last_compaction': 4, 'deliveries': []}
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_'):
            inv.recheck(saved, self.catalog, self.entry, self.receipts, compacted, maximum_bytes=65536)
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_'):
            self.save(self.submission(absence=True), audit=compacted)
        # A real re-read, in the new context, can establish coverage again.
        fresh = {**compacted, 'deliveries': [{'call_id': 'reread', 'response_sha256': 'page-hash', 'position': 7}]}
        receipts = self.receipts + [inv.receipt(self.catalog, 'fresh-thread', 'reread', self.entry['units'], 'page-hash')]
        self.assertEqual(self.save(receipts=receipts, audit=fresh)['completion'], 'complete')
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_RECEIPT_INVALID$'):
            self.save(audit={**compacted, 'deliveries': self.audit['deliveries']})

    def test_partial_unknown_cannot_be_consumed_as_complete(self):
        submission = {'claims': [{'id': 'gap', 'kind': 'unknown', 'statement': 'Unfinished.',
            'confidence': 'unknown', 'citations': [], 'searched_sets': [], 'unknowns': 'All pages remain.', 'contrary': []}],
            'decisions': []}
        saved = self.save(submission, receipts=[])
        self.assertEqual(saved['completion'], 'partial')
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_CHANGED$'):
            inv.recheck(saved, self.catalog, self.entry, [], self.audit, maximum_bytes=65536)
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_COVERAGE_INCOMPLETE$'):
            value = self.submission(absence=True); value['claims'][0]['searched_sets'] = []
            self.save(value)

    def test_citations_caps_and_foreign_receipts_refuse(self):
        for corruption in ('hash', 'id', 'prose-only', 'decision'):
            s = self.submission()
            if corruption in ('hash', 'id'):
                s['claims'][0]['citations'][0]['sha256' if corruption == 'hash' else 'id'] = 'wrong'
            elif corruption == 'prose-only': s['claims'][0]['citations'] = []
            else: s['decisions'][0]['claims'] = ['unknown']
            with self.subTest(corruption=corruption), self.assertRaisesRegex(ValueError, '^INVESTIGATION_'):
                self.save(s)
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_CHECKPOINT_TOO_LARGE$'):
            inv.checkpoint(self.catalog, self.entry, self.submission(), self.receipts, self.audit, maximum_bytes=100)
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_RECEIPT_INVALID$'):
            self.save(receipts=[{**self.receipts[0], 'session_id': 'other-thread'}])

    def test_checked_record_pages_keep_every_edit_field_and_preimage(self):
        ids = sorted({r['record_id'] for r in self.catalog['evidence'].values()
                      if r['kind'] == 'record' and r['scope'] == 'local'},
                     key=lambda r: self.model.ranges[self.model.node(r)])
        expected = [navigation.Navigation(self.model).record(self.model.node(r)) for r in ids]
        actual = []; offset = 0
        while offset is not None:
            page = inv.record_page(self.catalog, self.model, ids, offset=offset, limit=7)
            actual.extend(corridor_capacity.expand(page)); offset = page['next_offset']
        self.assertEqual(actual, expected)
        self.assertTrue(all('preimage_sha256' in r for r in actual))
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_PLAN_INVALID$'):
            inv.record_page(self.catalog, self.model, ['unknown'])
        with self.assertRaisesRegex(ValueError, '^INVESTIGATION_CHANGED$'):
            changed = copy.deepcopy(self.catalog); changed['binding']['generation'] = 'changed'
            inv.record_page(changed, self.model, ids)


class NativeCoverageTests(unittest.TestCase):
    def read(self, events):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder); (root/'sessions').mkdir()
            (root/'sessions/rollout-test.jsonl').write_text(''.join(json.dumps(e)+'\n' for e in events))
            return client.session_delivery_window(root, 'thread')

    def events(self, remote):
        f = native_fixture.CompactionTests()
        checkpoint = f.checkpoint(remote)
        before = {'type': 'function_call', 'name': 'operation', 'call_id': 'before', 'arguments': '{}'}
        output = {'type': 'function_call_output', 'call_id': 'before', 'output': 'page-one'}
        checkpoint['replacement_history'].extend([before, output])
        checkpoint['replacement_history_metadata'].extend([{}, {}])
        response = lambda item: {'type': 'response_item', 'payload': item}
        return [{'type': 'session_meta', 'payload': {'id': 'thread'}},
                response({'type': 'additional_tools', 'tools': native_fixture.DECLARATION}),
                response(before), response(output), {'type': 'compacted', 'payload': checkpoint},
                response({'type': 'function_call', 'name': 'operation', 'call_id': 'after', 'arguments': '{}'}),
                response({'type': 'function_call_output', 'call_id': 'after', 'output': 'page-two'})]

    def test_both_compaction_paths_ignore_retained_pages_and_count_only_real_redelivery(self):
        for remote in (False, True):
            with self.subTest(remote=remote):
                events = self.events(remote)
                before = self.read(events[:4])
                self.assertEqual([d['call_id'] for d in before['deliveries']], ['before'])
                after = self.read(events)
                self.assertEqual([d['call_id'] for d in after['deliveries']], ['after'])
                self.assertGreater(after['deliveries'][0]['position'], after['last_compaction'])
                # A later compaction after checkpoint submission also voids it.
                self.assertEqual(self.read(events + [events[4]])['deliveries'], [])

    def test_malformed_compaction_and_unpaired_output_fail_closed(self):
        events = self.events(False)
        for bad in ('shape', 'unpaired', 'duplicate'):
            changed = copy.deepcopy(events)
            if bad == 'shape': del changed[4]['payload']['window_number']
            elif bad == 'unpaired': changed[-1]['payload']['call_id'] = 'missing'
            else: changed.append(changed[-1])
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, '^CODEX_'):
                self.read(changed)


if __name__ == '__main__':
    unittest.main()
