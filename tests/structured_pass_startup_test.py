"""Verbatim startup selection and a numeric, reserve-aware allowance."""
import copy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import startup_inputs as startup, edit_contract


CONTEXT = {'window_tokens': 258400, 'startup_tokens': 60000,
           'lifecycle_tokens': 48000, 'margin_tokens': 25840,
           'bytes_per_1000_tokens': 2580}


class StartupTests(unittest.TestCase):
    def test_verbatim_sections_ignore_example_anchors(self):
        first = '<a id="first"></a>\r\n## First\r\nFull prose — unchanged.\r\n'
        example = '```md\r\n<a id="fake"></a>\r\n```\r\n'
        second = '<a id="second"></a>\r\n## Second\r\nKeep this too.\r\n'
        data = (first+example+second).encode()
        self.assertEqual(startup.sections(data, ['first']), first+example)
        self.assertEqual(startup.sections(data, ['second']), second)
        self.assertEqual(startup.sections(data, ['first', 'second']), data.decode())
        self.assertEqual(startup.sections(data, ['*']), data.decode())
        for anchors in ([], ['fake'], ['first', 'first'], ['second', 'first'], [{}]):
            with self.subTest(anchors=anchors), self.assertRaises(ValueError):
                startup.sections(data, anchors)

    def test_allowance_preserves_lifecycle_margin_and_next_page(self):
        budget = startup.allowance(CONTEXT)
        self.assertEqual(budget['response_tokens'], 124560)
        self.assertEqual(budget['response_bytes'], 321364)
        self.assertEqual(budget['page_maximum_bytes'], 24576)
        text = startup.prompt({'budget': budget})
        for token in ('321364 bytes', '258400 tokens', '60000 tokens', '48000', '25840',
                      'both analogues', 'resumed turn', '24576-byte maximum', 'on demand'):
            self.assertIn(token, text)
        self.assertIn('separate lifecycle reserve',text)
        self.assertIn('They do not consume the investigation byte allowance',text)
        for key, value in [('margin_tokens', 25839), ('startup_tokens', 240000),
                           ('bytes_per_1000_tokens', True)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                startup.allowance({**CONTEXT, key: value})

    def test_missing_or_inflated_allowance_is_refused(self):
        original = startup.allowance(CONTEXT)
        for key in ('response_bytes', 'response_tokens', 'page_maximum_bytes'):
            for remove in (True, False):
                changed = copy.deepcopy(original)
                if remove:del changed[key]
                else:changed[key] += 1
                with self.subTest(key=key, remove=remove), self.assertRaisesRegex(ValueError, 'INPUT_CHANGED'):
                    startup.prompt({'budget': changed})

    def test_reference_serialization_preserves_every_field_and_prose(self):
        expected = edit_contract.reference(['projects/sample/docs/notes.md'])
        actual = edit_contract.text(['projects/sample/docs/notes.md'])
        self.assertEqual(json.loads(actual), json.loads(json.dumps(expected)))
        self.assertLess(len(actual), len(json.dumps(expected, indent=2).encode()))


if __name__ == '__main__':unittest.main()
