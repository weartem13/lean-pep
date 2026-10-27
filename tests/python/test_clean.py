"""Safety checks for the public cleanup allowlist, without touching a real project."""
from pathlib import Path
import tempfile,unittest,importlib.util
SPEC=importlib.util.spec_from_file_location('public_clean',Path(__file__).resolve().parents[2]/'scripts/clean.py')
clean=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(clean)

class CleanSafetyTests(unittest.TestCase):
    def test_dry_run_and_apply_preserve_inputs_and_dependencies(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d)
            retained=['data/cases/pg/capture.json','data/cases/pg/selected_exact.json','.lake/packages/mathlib/.lake/build/a.olean','.venv-pepit/x.pyc','paper/LeanPEP.pdf','paper/main.tex','LeanPEP/X.lean']
            for rel in retained:
                p=r/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('retained')
            for rel in ['.lake/build/lib/LeanPEP/X.olean','paper/build/main.aux','tools/__pycache__/x.pyc']:
                p=r/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('cache')
            items=clean.plan(r)
            self.assertEqual(len(items),3);self.assertTrue((r/'.lake/build').exists())
            clean.apply(r,items)
            for rel in retained:self.assertEqual((r/rel).read_text(),'retained')
    def test_target_symlink_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);(r/'paper').mkdir();(r/'data').mkdir();(r/'paper/build').symlink_to(r/'data',target_is_directory=True)
            with self.assertRaisesRegex(ValueError,'symlink'):clean.plan(r)
    def test_nested_symlink_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);(r/'.lake/build').mkdir(parents=True);(r/'data').mkdir();(r/'.lake/build/link').symlink_to(r/'data',target_is_directory=True)
            with self.assertRaisesRegex(ValueError,'symlink'):clean.plan(r)
    def test_raw_or_source_inside_cache_is_refused(self):
        for name in ['capture.json','selected_exact.json','selected.json','raw.json','Proof.lean']:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as d:
                r=Path(d);(r/'paper/build').mkdir(parents=True);(r/'paper/build'/name).write_text('protected')
                with self.assertRaisesRegex(ValueError,'protected'):clean.plan(r)
    def test_changed_plan_refuses_all_deletion(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);(r/'paper/build').mkdir(parents=True);items=clean.plan(r);(r/'tools/__pycache__').mkdir(parents=True)
            with self.assertRaisesRegex(ValueError,'changed'):clean.apply(r,items)
            self.assertTrue((r/'paper/build').exists())
