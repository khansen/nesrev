"""Compare delivered keys with the schemas reached by real dispatch methods."""
import io
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from structured_pass import bridge, declared_inputs, operation_contract as contract, service
from structured_pass.launcher import Corridor
from structured_pass.rename_service import RenameService
from structured_pass.retained_service import RetainedReviewService
from structured_pass.verdict_bridge import Bridge


class KeysAccepted(Exception):
    pass


def delivered(role, profile):
    listing = bridge.tool_listing(role, profile)['tools'][0]
    return listing, json.loads(listing['inputSchema']['properties']['arguments']['description'].split(contract.DESCRIPTION_MARKER)[1])


def dispatch_fixture(role, profile):
    # Only external state is stubbed. Dispatch and its argument checks are real.
    if profile == 'retained':
        instance = RetainedReviewService.__new__(RetainedReviewService)
        instance.config = {'profile': 'source-v2'}
    else:
        instance = Corridor.__new__(Corridor)
        instance.checked_editor = lambda: {}
        instance.ensure_handoff = lambda: 'ticket'
        instance.editor = RenameService.__new__(RenameService)
        verdict = Bridge.__new__(Bridge)
        verdict.config = {'role': role}
        instance.verdicts = lambda _: verdict
    return lambda operation, args: instance.dispatch(operation, args, role)


class ContractTests(unittest.TestCase):
    def test_captured_claude_declaration_matches_service(self):
        actual = json.loads((ROOT / 'tests/fixtures/claude_facts_tool_declaration.json').read_text())
        expected = bridge.tool_listing('reviewer')['tools'][0]
        self.assertEqual(actual['name'], bridge.TOOL)
        self.assertEqual(actual['description'], expected['description'])
        self.assertEqual(actual['input_schema'], expected['inputSchema'])

    def assert_dispatch_matches(self, role, profile, declaration=None):
        listing, expected = delivered(role, profile)
        expected = expected if declaration is None else declaration
        self.assertEqual(set(expected), set(listing['inputSchema']['properties']['operation']['enum']))
        dispatch = dispatch_fixture(role, profile)
        original = service.schema
        for operation, spec in expected.items():
            def stop_after_keys(args, required, optional=()):
                self.assertEqual(contract.keys((required, optional)),
                                 {k: spec[k] for k in ('required', 'optional')}, operation)
                original(args, required, optional)
                raise KeysAccepted()
            required = {k: None for k in spec['required']}
            cases = [(required, True), ({**required, **dict.fromkeys(spec['optional'])}, True),
                     ({**required, 'unexpected_argument': None}, False)]
            cases += [({k: v for k, v in required.items() if k != missing}, False)
                      for missing in spec['required']]
            for args, accepted in cases:
                with self.subTest(role=role, profile=profile, operation=operation, arguments=args):
                    with patch.object(service, 'schema', side_effect=stop_after_keys):
                        with self.assertRaises(KeysAccepted if accepted else ValueError) as caught:
                            dispatch(operation, args)
                        if not accepted:
                            self.assertEqual(str(caught.exception), 'REQUEST_SCHEMA')

    def test_each_offered_operation_matches_dispatch(self):
        for profile in ('corridor', 'retained'):
            for role in ('implementer', 'reviewer'):
                self.assert_dispatch_matches(role, profile)

    def test_dispatch_change_without_declaration_is_caught(self):
        _, frozen = delivered('implementer', 'corridor')
        with patch.dict(contract.BASE, {'validate': (('renamed_candidate_key',), ())}):
            # The same assertion used above must reject a declaration captured
            # before this deliberate dispatch-only mutation.
            dispatch = dispatch_fixture('implementer', 'corridor')
            observed = []
            def capture(args, required, optional=()):
                observed.append(contract.keys((required, optional)))
                raise KeysAccepted()
            with patch.object(service, 'schema', side_effect=capture):
                with self.assertRaises(KeysAccepted):
                    dispatch('validate', {})
            with self.assertRaises(AssertionError):
                self.assertEqual(frozen['validate'], observed[0])
            self.assertEqual(delivered('implementer', 'corridor')[1]['validate'], observed[0])

    def test_image_keys_come_from_enforced_conditional_schema(self):
        _, declaration = delivered('implementer', 'corridor')
        spec = declaration['input']['reference_image']
        self.assertEqual(spec, {'required': ['generation', 'input_id'], 'optional': []})
        original = contract.check
        def capture(value, enforced):
            self.assertEqual(contract.keys(enforced), spec)
            original(value, enforced)
            raise KeysAccepted()
        with patch.object(declared_inputs, 'load', return_value={'items': [{'id': 'page', 'kind': 'reference_image'}]}):
            with patch.object(contract, 'check', side_effect=capture):
                with self.assertRaises(KeysAccepted):
                    declared_inputs.implementer_read('unused', 'generation', 'page')
                for extra in ({'offset': 0}, {'limit': 1}, {'path': 'elsewhere'}):
                    with self.assertRaisesRegex(ValueError, '^REQUEST_SCHEMA$'):
                        declared_inputs.implementer_read('unused', 'generation', 'page', **extra)
        for role, profile in (('reviewer', 'corridor'), ('implementer', 'retained'), ('reviewer', 'retained')):
            self.assertNotIn('reference_image', delivered(role, profile)[1]['input'])

    def test_listing_has_all_smoke_dependency_keys_and_fits_text_cap(self):
        expected = {
            'validate': {'cid'}, 'publish': {'cid'}, 'request-changes': {'ticket', 'report'},
            'review': {'ticket', 'generation', 'base_generation', 'offset', 'limit'},
            'review_report': {'sequence', 'offset', 'limit'}, 'input': {'generation', 'input_id', 'offset', 'limit'},
            'confirm': {'generation', 'preview_digest'},
        }
        for role in ('implementer', 'reviewer'):
            listing, declarations = delivered(role, 'corridor')
            self.assertLessEqual(len(listing['description']), 4096)
            self.assertLessEqual(len(listing['inputSchema']['properties']['arguments']['description']), 4096)
            self.assertLess(len(json.dumps({'jsonrpc': '2.0', 'id': 1, 'result': {'tools': [listing]}}).encode()), 24576)
            for op, fields in expected.items():
                if op in declarations:
                    self.assertEqual(set(declarations[op]['required'] + declarations[op]['optional']), fields)

    def test_schema_error_returns_same_expected_keys_without_retry(self):
        requests = [
            {'jsonrpc': '2.0', 'id': 1, 'method': 'tools/call', 'params': {'name': 'operation',
             'arguments': {'operation': 'validate', 'arguments': {'candidate': 'C1'}}}},
        ]
        instance = Corridor.__new__(Corridor)
        dispatch = dispatch_fixture('implementer', 'corridor')
        instance.dispatch = lambda operation, args, role: dispatch(operation, args)
        instance.error_context = lambda _: {'generation': 'G-start'}
        output = io.StringIO()
        with patch('structured_pass.launcher.Corridor', return_value=instance):
            bridge.mcp('unused', 'implementer', input_stream=map(json.dumps, requests), output_stream=output)
        result = json.loads(output.getvalue())['result']
        error = json.loads(result['content'][0]['text'])
        self.assertTrue(result['isError'])
        self.assertEqual(error, {'error': 'REQUEST_SCHEMA', 'expected_arguments': {'required': ['cid'], 'optional': []},
                                 'retryable': False, 'generation': 'G-start'})


if __name__ == '__main__':
    unittest.main()
