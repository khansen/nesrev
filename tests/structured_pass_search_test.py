"""Typed search: native facts, admitted text, complete bounded transport."""
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'scripts'), str(ROOT/'tests')]
from structured_pass import search, producer, bridge, review_pages
from structured_pass.model import certify
import structured_pass_evidence_test as evidence_fixture
import structured_pass_fixture as fixture


def all_pages(call, query, **kwargs):
    pages = []; continuation = None
    while True:
        page = call(query=query, continuation=continuation, **kwargs)
        pages.append(page)
        if page['complete']:
            break
        continuation = page['continuation']
        if len(pages) > 2000:
            raise AssertionError('non-progressing continuation')
    return pages, [row for p in pages for row in p['rows']]


class InstructionSearchTests(unittest.TestCase):
    setUp = evidence_fixture.EvidenceTests.setUp

    def query(self, *predicates, **extra):
        return search.instruction_rows(self.model,
            {'kind': 'instructions', 'alternatives': [[p] for p in predicates], **extra})

    def test_native_value_modes_shapes_and_pointer_meaning(self):
        rows, summary = self.query({'values': [0x40], 'operand': 'non_immediate'})
        self.assertEqual(summary['total_matches'], 4)
        self.assertEqual({r['instruction']['expression_shape'] for r in rows}, {'bound'})
        indexed = [r['instruction'] for r in rows if r['instruction']['final_mode'] == 'ZEROPAGE_X_MODE']
        self.assertEqual(indexed[0]['operand_meaning'], 'indexed_base')
        self.assertEqual(indexed[0]['operand_value'], 0x40)
        rows, _ = self.query({'values': [0xFF], 'modes': ['POSTINDEXED_INDIRECT_MODE']})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]['instruction']['operand_meaning'], 'pointer_expression')
        self.assertIsNotNone(rows[0]['instruction']['memory_access']['pointer'])
        rows, _ = self.query({'values': [0x40], 'operand': 'immediate'})
        self.assertEqual({r['instruction']['mnemonic'] for r in rows}, {'CMP', 'LDA'})
        self.assertTrue(all(r['instruction']['operand_meaning'] == 'immediate_value' for r in rows))
        rows, _ = self.query({'shapes': ['compound'], 'values': [0x41]})
        self.assertEqual({r['instruction']['mnemonic'] for r in rows}, {'STA'})

    def test_range_and_context_do_not_cross_data_or_segments(self):
        rows, summary = self.query({'ranges': [[0x3F, 0x40]], 'shapes': ['literal']})
        self.assertEqual(summary['total_matches'], 1)
        self.assertEqual(rows[0]['instruction']['operand_value'], 0x3F)
        # The last RTS before the table must not be adjacent to the overlaid JSR.
        rows, summary = search.instruction_rows(self.model, {'kind': 'instructions',
            'alternatives': [[{'mnemonics': ['RTS']}, {'mnemonics': ['JSR']}]]})
        self.assertEqual(summary['total_matches'], 0)
        rows, _ = self.query({'mnemonics': ['JMP']}, context={'before': 2, 'after': 2})
        self.assertEqual([r['relative_instruction'] for r in rows], [-2, -1, 0, 1, 2])
        self.assertEqual([r['part'] for r in rows], ['context', 'context', 'match', 'context', 'context'])

    def test_zero_context_keeps_every_match_owner_and_uncertainty(self):
        query={'kind':'instructions','alternatives':[[{'operand':'non_immediate'}]]}
        wide,wide_meta=search.instruction_rows(self.model,{**query,'context':{'before':3,'after':3}})
        narrow,narrow_meta=search.instruction_rows(self.model,{**query,'context':{'before':0,'after':0}})
        fields=('witness_id','alternative','certainty','relative_instruction','instruction')
        expected=[{k:r[k] for k in fields} for r in wide if r['part']=='match']
        self.assertEqual([{k:r[k] for k in fields} for r in narrow],expected)
        self.assertTrue(all(r['part']=='match' for r in narrow))
        for key in ('total_matches','unresolved_candidates','complete_numeric_answer'):
            self.assertEqual(narrow_meta[key],wide_meta[key])

    def test_match_detail_is_an_explicit_projection_of_every_full_match(self):
        query={'kind':'instructions','alternatives':[[{'operand':'non_immediate','values':[0x40]}]]}
        def compare():
            full,meta=search.instruction_rows(self.model,query)
            small,summary=search.instruction_rows(self.model,{**query,'detail':'matches'})
            expected=[{**r,'instruction':{k:r['instruction'][k] for k in search.MATCH_FIELDS}} for r in full]
            self.assertEqual(list(small),expected)
            self.assertTrue(expected)
            self.assertIn('owner_id',search.MATCH_FIELDS)
            self.assertIn('record_id',search.MATCH_FIELDS)
            for key in ('total_matches','unresolved_candidates','complete_numeric_answer'):
                self.assertEqual(summary[key],meta[key])
            self.assertEqual(summary['instruction_fields'],list(search.MATCH_FIELDS))
            pages,encoded=all_pages(lambda query,continuation,limit:search.page(small,summary,'match-test',continuation,limit),{},limit=2)
            decoded=[]
            for page in pages:
                self.assertEqual(page['encoding'],'instruction-matches-columnar-v1')
                for values in page['rows']:
                    row={**page['constants'],'instruction':{}}
                    self.assertEqual(len(values),len(page['columns']))
                    for key,value in zip(page['columns'],values):
                        if key.startswith('instruction.'):row['instruction'][key.split('.')[1]]=value
                        else:row[key]=value
                    decoded.append(row)
            self.assertEqual(decoded,expected)
            return summary
        compare()
        instruction=next(i for i in self.model.instructions.values()
                         if i['operands'] and i['addressing_mode']!='IMMEDIATE_MODE')
        with patch.dict(instruction,operand_value=None):
            self.assertGreater(compare()['unresolved_candidates'],0)
        for detail,context in [('compact',{}),('matches',{'before':1}),('matches',{'after':1})]:
            with self.subTest(detail=detail,context=context),self.assertRaisesRegex(ValueError,'SEARCH_SCHEMA'):
                search.instruction_rows(self.model,{**query,'detail':detail,'context':context})

    def test_owner_and_overlay_identities_are_not_cpu_addresses(self):
        rows, _ = self.query({'mnemonics': ['JSR']})
        self.assertGreater(len(rows), 3)
        self.assertEqual(len({r['instruction']['record_id'] for r in rows}), len(rows))
        owner = self.model.ids[self.model.declarations['Overlaid']]
        selected, summary = self.query({'mnemonics': ['JSR']}, owner_id=owner)
        self.assertEqual(summary['total_matches'], 1)
        self.assertEqual(selected[0]['instruction']['owner_id'], owner)
        with self.assertRaises(ValueError):
            self.query({'mnemonics': ['JSR']}, owner_id='foreign-record')

    def test_native_sequence_positive_and_data_gap_negative(self):
        source = self.root/'sequence.asm'; binary = self.root/'sequence.bin'
        text = b'.ORG $C000\nEntry: PLA\n; a comment is not an instruction\nLocal: PLA\nPHA\nRTS\nPHA\n.DB 0\nRTS\n'
        source.write_bytes(text)
        subprocess.run([str(producer.EXE), '--pure-binary', str(source), '-o', str(binary)], check=True, capture_output=True)
        raw = binary.read_bytes(); padding = b'A'*(16384-len(raw))
        source.write_bytes(text+b'.DB "'+padding+b'"\n.END\n')
        reference = self.root/'sequence.nes'; reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+raw+padding)
        model, _ = certify(source, self.root/'sequence-capture', reference)
        rows, result = search.instruction_rows(model, {'kind': 'instructions', 'alternatives': [
            [{'mnemonics': ['PLA']}, {'mnemonics': ['PLA']}],
            [{'mnemonics': ['PHA']}, {'mnemonics': ['RTS']}]]})
        self.assertEqual(result['total_matches'], 2)
        self.assertEqual([r['instruction']['mnemonic'] for r in rows], ['PLA', 'PLA', 'PHA', 'RTS'])

    def test_unknown_is_not_zero_and_native_unknown_is_refused(self):
        # Defensive unit control only; this is not a certified unresolved model.
        ins = copy.deepcopy(next(i for i in self.model.instructions.values() if i['operands']))
        ins['operand_value'] = None
        self.assertIsNone(search.matches(ins, 'bound', {'values': [0]}))
        self.assertIs(search.matches(ins, 'bound', {'mnemonics': ['BRK'], 'values': [0]}), False)
        source = self.root/'unknown.asm'; source.write_text('.ORG $C000\nLDA UnknownName\n.END\n')
        with self.assertRaisesRegex(producer.ProducerRejected, 'PRODUCER_CERTIFICATION_FAILED'):
            producer.produce(source, self.root/'unknown-capture', self.root/'sample.nes')

    def test_unsupported_or_excessive_queries_refused(self):
        for pred in ({'regex': '.*'}, {'values': [True]}, {'ranges': [[9, 1]]},
                     {'values': list(range(33))}, {'mnemonics': ['FAKE']},
                     {'modes': ['abs']}, {'shapes': ['text']}, {}):
            with self.subTest(pred=pred), self.assertRaisesRegex(ValueError, 'SEARCH_SCHEMA'):
                self.query(pred)
        with self.assertRaisesRegex(ValueError, 'SEARCH_SCHEMA'):
            self.query({'mnemonics': ['LDA']}, context={'before': 11})


class TextSearchTests(unittest.TestCase):
    def rows(self, text, **query):
        item = {'input_id': 'T-test', 'path': 'document.md', 'sha256': authored_hash(text),
                'kind': 'document', 'available': True}
        return search.text_rows([(item, text.encode())], {'kind': 'text', 'inputs': ['T-test'], **query})

    def test_unicode_fold_positions_and_q09_token_boundaries(self):
        text = 'Straße STRASSE foo foo_bar @foo foo@ foo-bar FOO\n'
        rows, summary = self.rows(text, terms=['STRASSE', 'foo'], ignore_case=True, whole_token=True)
        positions = [(['STRASSE', 'foo'][m['term_index']], m['start'], m['end'])
                     for r in rows for m in r['matches']]
        self.assertEqual(positions, [('STRASSE', 0, 6), ('STRASSE', 7, 14),
                                    ('foo', 15, 18), ('foo', 37, 40), ('foo', 45, 48)])
        self.assertEqual(summary['total_matches'], 1)
        # A half of an expanding fold is not a full original character match.
        self.assertEqual(list(search.occurrences('ß', 's', True, False, False)), [])
        self.assertEqual(list(search.occurrences('ß', 'ss', True, False, False)), [(0, 1)])

    def test_prefix_literal_punctuation_context_and_absence(self):
        rows, summary = self.rows('lead\n# title\n  # title\nvalue [$x]\ntail\n',
            prefixes=['#'], terms=['[$x]'], context={'before': 1, 'after': 1})
        self.assertEqual(summary['total_matches'], 2)
        self.assertEqual({r['match_line'] for r in rows}, {2, 4})
        self.assertEqual({r['line'] for r in rows if r['part'] == 'line'}, {1, 2, 3, 4, 5})
        rows, summary = self.rows('absent', terms=['present'])
        self.assertEqual((list(rows), summary['total_matches']), ([], 0))

    def test_long_dense_line_reconstructed_without_omissions(self):
        text = 'needle' + '🦆'*3000 + 'needle'
        rows, summary = self.rows(text, terms=['needle'])
        self.assertEqual(summary['total_matches'], 1)
        self.assertEqual(''.join(r['text'] for r in rows if r['part'] == 'line'), text)
        pages, got = all_pages(lambda query, continuation, limit: search.page(rows,
            {'generation': 'G', **summary}, 'binding', continuation, limit), {}, limit=3)
        self.assertGreater(len(pages), 2)
        self.assertEqual(got, list(rows))
        self.assertTrue(all(review_pages.wire_size(p) <= review_pages.BUDGET for p in pages))
        self.assertTrue(pages[-1]['complete'])
        dense, _ = self.rows('a'*1100, terms=['a'])
        self.assertEqual(sum(len(r['matches']) for r in dense), 1100)
        self.assertTrue(all(len(r['matches']) <= 8 for r in dense))

    def test_full_page_later_page_and_stale_token(self):
        rows = [{'line': i, 'text': 'unique' if i == 40 else 'common'} for i in range(41)]
        first = search.page(rows, {}, 'A', None, 40)
        self.assertEqual(first['total_rows'],len(rows))
        self.assertEqual(first['minimum_response_bytes'],
            sum(len(json.dumps(json.dumps(r)).encode())-2 for r in rows))
        self.assertFalse(first['complete'])
        self.assertEqual(len(first['rows']), 40)
        last = search.page(rows, {}, 'A', first['continuation'], 40)
        self.assertEqual(last['rows'], [rows[-1]])
        self.assertTrue(last['complete'])
        self.assertEqual(first['minimum_response_bytes'],last['minimum_response_bytes'])
        self.assertLess(first['minimum_response_bytes'],sum(review_pages.wire_size(p) for p in (first,last)))
        self.assertIsNone(search.page(rows[:40], {}, 'A', None, 40)['continuation'])
        for token in (first['continuation'], 'not a token', 'W10='):
            with self.assertRaisesRegex(ValueError, 'SEARCH_CONTINUATION_INVALID'):
                search.page(rows, {}, 'B', token, 40)


def authored_hash(text):
    import hashlib
    return hashlib.sha256(text.encode()).hexdigest()


class SearchServiceTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):
            self.skipTest('pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(dir=ROOT/'tmp'); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.controller = fixture.prepare(self.root, uses=45,
            notes='\n'.join(f'needle row {n}' for n in range(46))+'\n')
        self.editor = self.controller.editor
        self.g = self.editor.state['current']

    def call(self, query, role='reviewer', **kwargs):
        return self.controller.dispatch('search', {'generation': self.g, 'query': query, **kwargs}, role)

    def test_both_roles_read_without_mutating_and_catalogue_excludes_unadmitted(self):
        before = self.editor.state_path.read_bytes()
        a = self.call({'kind': 'catalogue'})
        b = self.call({'kind': 'catalogue'}, role='implementer')
        self.assertEqual(a, b)
        paths = {r['path'] for r in a['rows']}
        self.assertIn('AGENTS.md', paths)
        self.assertIn(fixture.PROJECT+'docs/reverse_engineering/WORKING_NOTES.md', paths)
        self.assertNotIn(fixture.PROJECT+'docs/reverse_engineering/PROGRESS_SCORECARD.md', paths)
        self.assertFalse(any('/asm/' in p or p.endswith('.nes') for p in paths))
        selected = next(r for r in a['rows'] if r['path'].endswith('WORKING_NOTES.md'))
        query = {'kind': 'text', 'inputs': [selected['input_id']], 'terms': ['needle']}
        pages, rows = all_pages(self.call, query)
        self.assertEqual(pages[0]['total_matches'], 46)
        self.assertEqual({r['match_line'] for r in rows}, set(range(1, 47)))
        self.assertEqual(before, self.editor.state_path.read_bytes())
        for foreign in ('../../AGENTS.md', 'T-foreign', fixture.SOURCE):
            with self.assertRaisesRegex(ValueError, 'SEARCH_INPUT_UNKNOWN'):
                self.call({**query, 'inputs': [foreign]})
        missing = next(r for r in a['rows'] if not r['available'])
        with self.assertRaisesRegex(ValueError, 'SEARCH_INPUT_UNAVAILABLE'):
            self.call({**query, 'inputs': [missing['input_id']]})

    def test_query_and_generation_tokens_and_input_drift(self):
        q = {'kind': 'instructions', 'alternatives': [[{'mnemonics': ['LDA']}]]}
        first = self.call(q, limit=1)
        with self.assertRaisesRegex(ValueError, 'SEARCH_CONTINUATION_INVALID'):
            self.call({**q, 'context': {'after': 1}}, continuation=first['continuation'])
        # Same underlying model but a different published identity is distinct.
        with self.assertRaisesRegex(ValueError, 'SEARCH_CONTINUATION_INVALID'):
            self.editor.search(self.g, q, first['continuation'], public_generation='E-other')
        with self.assertRaisesRegex(ValueError, 'UNKNOWN_GENERATION'):
            self.controller.dispatch('search', {'generation': 'G-missing', 'query': q}, 'reviewer')
        record = self.editor.state['generations'][self.g]
        source = Path(record['checkout'])/self.editor.source
        source.write_bytes(source.read_bytes()+b'\n')
        with self.assertRaisesRegex(ValueError, 'GENERATION_INPUT_CHANGED'):
            self.call(q)

    def test_historical_reads_and_external_artifact_generation_binding(self):
        q = {'kind': 'instructions', 'alternatives': [[{'mnemonics': ['LDA']}]]}
        old = self.call(q, limit=1)
        preview = self.editor.preview(self.g, fixture.rename_ops(self.controller, self.g))
        cid = self.editor.confirm(self.g, preview['preview_digest'])['candidate']
        validated = self.editor.validate(cid)
        self.assertEqual(validated['status'], 'validated', validated)
        published = self.controller.dispatch('publish', {'cid': cid}, 'implementer')
        new = self.editor.state['current']
        self.assertNotEqual(new, self.g)
        historic = self.call(q, continuation=old['continuation'], limit=1)
        self.assertEqual(historic['generation'], self.g)
        self.assertEqual(historic['offset'], 1)
        external = published['review']['artifact_id']
        response = self.controller.dispatch('search', {'generation': external, 'query': q, 'limit': 1}, 'reviewer')
        self.assertEqual(response['generation'], external)
        with self.assertRaisesRegex(ValueError, 'SEARCH_CONTINUATION_INVALID'):
            self.controller.dispatch('search', {'generation': new, 'query': q,
                'continuation': response['continuation']}, 'reviewer')

    def test_wire_schema_and_both_role_tool_lists(self):
        for role in ('reviewer', 'implementer'):
            out = io.StringIO()
            requests = [{'jsonrpc': '2.0', 'id': 1, 'method': 'tools/list'},
                {'jsonrpc': '2.0', 'id': 2, 'method': 'tools/call', 'params': {'name': 'operation',
                 'arguments': {'operation': 'search', 'arguments': {'generation': self.g,
                    'query': {'kind': 'instructions', 'alternatives': [[{'mnemonics': ['LDA']}]]}}}}}]
            bridge.mcp(self.controller.root, role, input_stream=io.StringIO('\n'.join(map(json.dumps, requests))), output_stream=out)
            lines = out.getvalue().splitlines(); declared = json.loads(lines[0])
            self.assertIn('search', declared['result']['tools'][0]['inputSchema']['properties']['operation']['enum'])
            self.assertNotIn('isError', json.loads(lines[1])['result'])
            self.assertLessEqual(len(lines[1].encode())+1, 24*1024)
        with self.assertRaisesRegex(ValueError, 'REQUEST_SCHEMA'):
            self.controller.dispatch('search', {'generation': self.g, 'query': {'kind': 'catalogue'},
                'public_generation': 'untrusted'}, 'reviewer')


if __name__ == '__main__':
    unittest.main()
