"""Decode the delivered contract and compare every native edit operand."""
import copy
import json
import math
import unittest
from unittest.mock import patch

import structured_pass_evidence_test as fixture
from structured_pass import (navigation, edit_records, evidence_views, source_edits,
                             corridor_capacity, edit_contract, review_pages)


def decode(page):
    expressions = {row[0]: dict(zip(page['expression_columns'], row)) for row in page['expressions']}
    def expression(ident):
        row = expressions[ident]
        return {'record_id': ident, **row['fields'], 'preimage': page['preimages'][row['preimage']],
                'children': [expression(child) for child in row['children']]}
    result = []
    for values in page['records']:
        row = dict(zip(page['columns'], values))
        row['preimage'] = page['preimages'][row['preimage']]
        row['expressions'] = [expression(ident) for ident in row['expressions']]
        result.append(row)
    return result


def full_inputs(model, ident):
    node = model.node(ident); record = navigation.Navigation(model).record(node)
    def expression(row):
        return {**row, 'preimage': evidence_views.identity(model, model.node(row['record_id']))['preimage'],
                'children': [expression(child) for child in row['children']]}
    return {'record_id': record['record_id'], 'kind': record['kind'], 'name': record.get('name'),
            'text': model.source[slice(*model.ranges[node])].decode(),
            'preimage': record['preimage_sha256'], 'owner_id': record['lexical_owner_id'],
            'expressions': [expression(row) for row in record['expressions']]}


def argument_inputs(rows):
    """All record-sourced fields; authored new names/text are deliberately absent."""
    result = {kind: [] for kind in ('rename', 'declare', 'replace_expression',
                                    'delete_declaration', 'localize', 'reflow_data', 'comment_insert')}
    def expressions(values):
        for row in values:
            result['replace_expression'].append({'expression_id': row['record_id'],
                'preimage': row['preimage'], 'original': {k:v for k,v in row.items() if k not in ('children','preimage')}})
            expressions(row['children'])
    for row in rows:
        ident = row['record_id']; preimage = row['preimage']
        for kind in ('declare', 'comment_insert'):
            result[kind].append({'anchor_id': ident, 'preimage': preimage})
        if row['name'] is not None:
            result['rename'].append({'declaration_id': ident, 'old_name': row['name'], 'preimage': preimage})
            result['delete_declaration'].append({'declaration_id': ident, 'preimage': preimage})
            result['localize'].append({'declaration_id': ident, 'preimage': preimage, 'scope_id': row['owner_id']})
        result['reflow_data'].append({'record_ids': [ident], 'preimages': [preimage],
            'groups': [[e['record_id'] for e in row['expressions']]]})
        expressions(row['expressions'])
    return result


class EditRecordTests(unittest.TestCase):
    def setUp(self):
        fixture.EvidenceTests.setUp(self)
        self.nav = navigation.Navigation(self.model)
        # Exclude only the fixture's artificial multi-kilobyte padding string.
        self.ids = [self.model.ids[n] for n in self.nav.statements
                    if self.model.ranges[n][1]-self.model.ranges[n][0] < 1024]

    def test_all_native_operands_and_arguments_match_full_records(self):
        actual = []; offset = 0
        while offset is not None:
            page = self.nav.query('edit', record_id=self.ids, offset=offset, limit=7)
            actual.extend(decode(page)); offset = page['next_offset']
            self.assertLessEqual(review_pages.wire_size(page), review_pages.BUDGET-4096)
        expected = [full_inputs(self.model, ident) for ident in self.ids]
        self.assertEqual(actual, expected)
        self.assertEqual(argument_inputs(actual), argument_inputs(expected))
        self.assertTrue(argument_inputs(actual)['replace_expression'])
        for value in argument_inputs(actual)['replace_expression']:
            source_edits.selected(self.model, value['expression_id'], value['preimage'])
        literal = next(e for r in actual for e in r['expressions'] if e.get('kind') == 'INTEGER_NODE')
        op = {'kind':'replace_expression','reason':'Same native value.','expression_id':literal['record_id'],
              'preimage':literal['preimage'],'expression':{'integer':literal['value']}}
        source_edits.plan(self.model, [op])

    def test_selection_and_size_cap_never_expand_or_skip_targets(self):
        for ident in self.ids:
            page = self.nav.query('edit', record_id=ident)
            self.assertEqual([r['record_id'] for r in decode(page)], [ident])
        offset = 0; actual = []
        with patch.object(review_pages, 'BUDGET', 8000):
            while offset is not None:
                page = self.nav.query('edit', record_id=self.ids, offset=offset, limit=40)
                actual.extend(r['record_id'] for r in decode(page)); offset = page['next_offset']
        self.assertEqual(actual, self.ids)
        for kwargs in ({'span':'segment'}, {'contains':'x'}, {'symbol':'Entry'}, {'limit':41}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                self.nav.query('edit', record_id=self.ids, **kwargs)
        padding = next(n for n in self.nav.statements if self.model.ranges[n][1]-self.model.ranges[n][0] >= 1024)
        with self.assertRaisesRegex(ValueError, '^RESPONSE_TOO_LARGE$'):
            self.nav.query('edit', record_id=self.model.ids[padding])

    def test_measured_response_rate_keeps_prior_request_hash_charge(self):
        page = self.nav.query('edit', record_id=self.ids[:10])
        args = {'generation':'G-'+'a'*64,'record_id':self.ids[:10],'view':'edit'}
        call = {'job':'edit','operation':'navigate','arguments':args,'wire_bytes':10000,'result':page}
        budget = {'window_tokens':258400,'startup_tokens':82000,'lifecycle_tokens':48000,
                  'margin_tokens':25840,'bytes_per_1000_tokens':2580}
        prices = {'initial_tokens':100,'overhead_bytes':36751,'overhead_request_bytes':1088}
        result = corridor_capacity.price([call], budget, **prices)
        response_hashes = edit_records.hash_characters(page)
        hashes = edit_records.hash_characters([page,args])
        self.assertEqual(result['edit_request_hash_characters_at_one_token_each'],64)
        self.assertEqual(result['edit_response_hash_characters_at_measured_rate'],response_hashes)
        ordinary = corridor_capacity.price([{**call,'result':{}}], budget, **prices)
        request = len(json.dumps({'operation':'navigate','arguments':args}).encode())
        old_combined=math.ceil((10000+request-hashes)*1000/2580)+hashes
        old_response=math.ceil((10000-response_hashes)*1000/2580)+response_hashes
        extra=old_combined-old_response+math.ceil(10000*1000/2398)-math.ceil((10000+request)*1000/2580)
        self.assertEqual(result['estimated_tokens']-ordinary['estimated_tokens'], extra)
        self.assertEqual(result['required_bytes'], ordinary['required_bytes'])


if __name__ == '__main__':
    unittest.main()
