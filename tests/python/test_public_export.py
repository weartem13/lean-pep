"""Release packaging guards; no Lean, solver or network execution."""
from pathlib import Path
import contextlib
import io
import json
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from scripts import export


class PublicExportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'maintained'
        self.root.mkdir()
        self.patch = patch.object(export, 'ROOT', self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        for name in export.FILES:
            self.put(name, 'maintained ' + name)
        for name in export.DIRECTORIES:
            (self.root / name).mkdir()
        self.put('paper/LICENSE', 'test-only paper license')
        self.put('SOURCE_MANIFEST.json', 'before')

    def put(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)
        return path

    def run_export(self, *args):
        with contextlib.redirect_stdout(io.StringIO()):
            export.main(list(args))

    def test_snapshot_preserves_research_inputs_and_manifest_matches_bytes(self):
        retained = ['LeanPEP/Imported/Proof.lean', 'data/cases/capture.json',
                    'data/cases/selected_exact.json', 'data/fixtures/generated/exact.json',
                    'data/paper/historical.log', 'data/paper/controls/initial/Contrasts.lean',
                    'docs/evidence/claim-evidence.json', 'docs/evidence/LICENSE']
        for name in retained:
            self.put(name, 'required input')
        for name in ['LICENSE', 'paper/LICENSE', 'NOTICE']:
            self.put(name, 'test-only authorized text')
        for name in ['.git/objects/private', '.env', 'old-draft.pdf',
                     'paper/build/main.pdf', 'paper/main.bbl', 'paper/main.fls', 'paper/main.vtc',
                     'paper/main.tex', 'paper/references.bib', 'paper/LeanPEP.pdf',
                     'paper/notes/editing-report.md', 'paper.zip',
                     *export.LOCAL_ONLY,
                     'tools/__pycache__/x.pyc', 'data/.lake/build/old.olean']:
            self.put(name, 'excluded')
        out = self.base / 'snapshot'
        self.run_export('--output', str(out))
        manifest = json.loads((out / 'PUBLIC_MANIFEST.json').read_text())
        self.assertEqual(set(manifest), {'public_id', 'source_id', 'files'})
        paths = {entry['path'] for entry in manifest['files']}
        self.assertTrue(set(retained + ['.gitignore', 'CITATION.cff', 'CHANGELOG.md',
                                       'LICENSE', 'NOTICE']) <= paths)
        self.assertFalse(any(x.startswith('paper/') for x in paths))
        self.assertFalse(paths & export.LOCAL_ONLY)
        self.assertNotIn('paper.zip', paths)
        source = json.loads((out / 'SOURCE_MANIFEST.json').read_text())
        self.assertEqual(source['files'], manifest['files'])
        self.assertEqual(source['source_id'], manifest['public_id'])
        self.assertFalse(any('private' in x or '.lake' in x or '__pycache__' in x
                             for x in paths))
        for entry in manifest['files']:
            self.assertEqual(export.digest(out / entry['path']), entry['sha256'])
        self.assertEqual(export.identity(manifest['files']), manifest['public_id'])
        self.assertEqual((out / 'SOURCE_MANIFEST.json').read_bytes(),
                         (self.root / 'SOURCE_MANIFEST.json').read_bytes())

    def test_bad_arguments_and_destinations_never_rewrite_source_manifest(self):
        existing = self.base / 'existing'
        existing.mkdir()
        link = self.base / 'link'
        link.symlink_to(self.base / 'missing')
        cases = [[], ['--output', str(existing)],
                 ['--output', str(self.root / 'nested')],
                 ['--output', str(link)],
                 ['--manifest-only', '--output', str(self.base / 'ambiguous')],
                 ['--manifest-only', '--bbl', str(self.base / 'old.bbl')]]
        for args in cases:
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises((ValueError, SystemExit)):
                    self.run_export(*args)
                self.assertEqual((self.root / 'SOURCE_MANIFEST.json').read_text(), 'before')
        self.assertFalse((self.root / 'nested').exists())
        self.assertFalse((self.base / 'missing').exists())

    def test_missing_input_and_manifest_symlink_refused_before_output(self):
        (self.root / 'CITATION.cff').unlink()
        out = self.base / 'missing-input'
        with self.assertRaisesRegex(ValueError, 'missing'):
            self.run_export('--output', str(out))
        self.assertFalse(out.exists())
        self.put('CITATION.cff', 'restored fixture')
        target = self.base / 'protected'
        target.write_text('do not touch')
        (self.root / 'SOURCE_MANIFEST.json').unlink()
        (self.root / 'SOURCE_MANIFEST.json').symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'regular'):
            self.run_export('--output', str(out))
        self.assertFalse(out.exists())
        self.assertEqual(target.read_text(), 'do not touch')

    def test_symlinks_and_nested_hidden_inputs_fail_closed(self):
        for name in ['tools/link.py', 'data/linked-dir', 'LICENSE']:
            p = self.root / name
            original = p.read_text() if p.is_file() else None
            if original is not None:
                p.unlink()
            p.symlink_to(self.base / 'outside')
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'symlink'):
                export.inventory()
            p.unlink()
            if original is not None:
                self.put(name, original)
        self.put('docs/.env', 'private fixture')
        with self.assertRaisesRegex(ValueError, 'hidden'):
            export.inventory()

    def test_manuscript_and_local_publication_changes_do_not_change_code_identity(self):
        before = export.identity(export.inventory())
        self.paper_fixture()
        for name in export.LOCAL_ONLY:
            self.put(name, 'local editorial metadata')
        self.assertEqual(before, export.identity(export.inventory()))
        (self.root / 'paper/LICENSE').unlink()
        self.assertEqual(before, export.identity(export.inventory()))
        self.put('data/paper/accepted.log', 'retained research evidence')
        self.assertNotEqual(before, export.identity(export.inventory()))

    def test_separate_paper_packaging_rejects_symlinked_license(self):
        bbl = self.paper_fixture()
        (self.root / 'paper/LICENSE').unlink()
        (self.root / 'paper/LICENSE').symlink_to(self.base / 'outside')
        out = self.base / 'unsafe-paper.zip'
        with self.assertRaisesRegex(ValueError, 'symlink'):
            self.run_export('--paper-output', str(out), '--bbl', str(bbl))
        self.assertFalse(out.exists())

    def paper_fixture(self):
        self.put('paper/main.tex', '\\input{preamble.tex}\n\\input{sections/body.tex}\n')
        self.put('paper/preamble.tex', '\\usepackage{natbib}\n')
        self.put('paper/sections/body.tex', '\\input{figures/one.tex}\n')
        self.put('paper/figures/one.tex', 'figure source')
        self.put('paper/references.bib', '@book{a,title={A}}')
        self.put('paper/README.md', 'test-only paper license scope statement')
        self.put('paper/notes/private.md', 'not an arXiv input')
        self.put('paper/claim-evidence.json', '{}')
        self.put('paper/unused.tex', 'not included')
        bbl = self.base / 'main.bbl'
        bbl.write_text('\\begin{thebibliography}{1}\\end{thebibliography}\n')
        return bbl

    def test_paper_archive_contains_only_referenced_inputs_and_supplied_bbl(self):
        bbl = self.paper_fixture()
        out = self.base / 'arxiv.zip'
        self.run_export('--paper-output', str(out), '--bbl', str(bbl))
        with zipfile.ZipFile(out) as archive:
            self.assertEqual(set(archive.namelist()), {
                'main.tex', 'preamble.tex', 'sections/body.tex', 'figures/one.tex',
                'references.bib', 'main.bbl', 'LICENSE', 'README.md'})
            self.assertEqual(archive.read('main.bbl'), bbl.read_bytes())
            for name in ['LICENSE', 'README.md']:
                self.assertEqual(archive.read(name), (self.root / 'paper' / name).read_bytes())
        self.assertEqual((self.root / 'SOURCE_MANIFEST.json').read_text(), 'before')

    def test_missing_license_or_scope_statement_creates_no_output(self):
        bbl = self.paper_fixture()
        cases = [('LICENSE', False), ('paper/LICENSE', True), ('paper/README.md', True)]
        for i, (name, paper) in enumerate(cases):
            p = self.root / name
            original = p.read_text()
            p.unlink()
            out = self.base / f'missing-license-{i}'
            args = ['--paper-output', str(out), '--bbl', str(bbl)] if paper else ['--output', str(out)]
            with self.subTest(name=name, paper=paper), self.assertRaises((ValueError, OSError)):
                self.run_export(*args)
            self.assertFalse(out.exists())
            self.assertEqual((self.root / 'SOURCE_MANIFEST.json').read_text(), 'before')
            self.put(name, original)

    def lipics_fixture(self):
        bbl = self.paper_fixture()
        self.put('paper/main.tex', '\\documentclass[a4paper,UKenglish]{lipics-v2021}\n'
                 '\\input{preamble.tex}\n\\input{sections/body.tex}\n'
                 '\\bibliographystyle{unsrturl}\n')
        self.put('paper/lipics-v2021.cls', '% test class, including its license header\n')
        self.put('paper/unsrturl.bst', '% test bibliography style and license header\n')
        self.put('paper/unused-style.bst', 'not selected')
        return bbl

    def test_selected_lipics_styles_are_bundled_byte_for_byte(self):
        bbl = self.lipics_fixture()
        out = self.base / 'lipics.zip'
        self.run_export('--paper-output', str(out), '--bbl', str(bbl))
        with zipfile.ZipFile(out) as archive:
            for name in ['lipics-v2021.cls', 'unsrturl.bst']:
                self.assertEqual(archive.read(name), (self.root / 'paper' / name).read_bytes())
            self.assertNotIn('unused-style.bst', archive.namelist())

    def test_missing_selected_style_creates_no_archive(self):
        bbl = self.lipics_fixture()
        for name in ['lipics-v2021.cls', 'unsrturl.bst']:
            p = self.root / 'paper' / name
            original = p.read_bytes()
            p.unlink()
            out = self.base / (name + '.zip')
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.run_export('--paper-output', str(out), '--bbl', str(bbl))
            self.assertFalse(out.exists())
            self.assertEqual((self.root / 'SOURCE_MANIFEST.json').read_text(), 'before')
            p.write_bytes(original)

    def test_paper_missing_unsafe_or_cyclic_input_creates_no_zip(self):
        bbl = self.paper_fixture()
        for i, name in enumerate(['missing.tex', '../escape.tex', 'main.tex']):
            self.put('paper/preamble.tex', '\\input{' + name + '}\n')
            out = self.base / f'rejected-{i}.zip'
            with self.subTest(name=name), self.assertRaises((ValueError, OSError)):
                self.run_export('--paper-output', str(out), '--bbl', str(bbl))
            self.assertFalse(out.exists())

    def test_paper_requires_bbl_and_does_not_overwrite_archive(self):
        bbl = self.paper_fixture()
        out = self.base / 'arxiv.zip'
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.run_export('--paper-output', str(out))
        out.write_bytes(b'prior archive')
        with self.assertRaisesRegex(ValueError, 'fresh'):
            self.run_export('--paper-output', str(out), '--bbl', str(bbl))
        self.assertEqual(out.read_bytes(), b'prior archive')


if __name__ == '__main__':
    unittest.main()
