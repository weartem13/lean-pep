"""Safety boundaries for the external deterministic-regeneration wrapper."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts import check_generated as check


class GeneratedCheckTests(unittest.TestCase):
    def test_source_output_and_existing_output_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaisesRegex(ValueError, 'outside'):
                check.fresh_output(root, root / 'new-output')
            self.assertFalse((root / 'new-output').exists())
            with self.assertRaisesRegex(ValueError, 'fresh'):
                check.fresh_output(root, root)

    def test_symlink_source_entry_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for directory in check.TREES:
                (root / directory).mkdir(parents=True)
            sentinel = root / 'selected_exact.json'
            sentinel.write_bytes(b'protected')
            (root / 'tools/link.py').symlink_to(sentinel)
            with self.assertRaisesRegex(ValueError, 'symbolic'):
                check.source_files(root)
            self.assertEqual(sentinel.read_bytes(), b'protected')

    def test_exact_values_and_lean_cannot_be_normalized(self):
        before = json.dumps({'bound': '1/4', 'path': 'examples/input.json'}).encode()
        after = json.dumps({'bound': '1/5', 'path': 'data/fixtures/input.json'}).encode()
        self.assertEqual(check.compare_payload('candidate.json', before, after)['status'], 'unexpected_difference')
        self.assertEqual(check.compare_payload('Replay.lean', b'-- examples/input.json',
                                             b'-- data/fixtures/input.json')['status'], 'unexpected_difference')

    def test_only_documentary_json_path_change_is_eligible(self):
        before = json.dumps({'path': 'examples/input.json', 'bound': '1/4'}).encode()
        after = json.dumps({'path': 'data/fixtures/input.json', 'bound': '1/4'}).encode()
        result = check.compare_payload('manifest.json', before, after)
        self.assertEqual(result['status'], 'documented_metadata_path_only')
        self.assertEqual(result['differences'][0]['path'], '/path')
        self.assertEqual(check.compare_payload('manifest.json', before, before)['status'], 'byte_identical')


if __name__ == '__main__':
    unittest.main()
