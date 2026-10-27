"""Source-integrity and clean-install guards for the public dependency entry."""
from pathlib import Path
import tempfile,unittest,importlib.util,json,hashlib,os
from unittest.mock import patch
SPEC=importlib.util.spec_from_file_location('public_setup',Path(__file__).resolve().parents[2]/'scripts/setup.py')
setup=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(setup)
REQUIRED=['lake-manifest.json','lean-toolchain','lakefile.lean','docs/pg-core-content-review.json','tools/replay_pg_certificate.py','scripts/setup.py']
def fixture(r):
    entries=[]
    for rel in REQUIRED:
        p=r/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(rel)
        entries.append(dict(path=rel,sha256=setup.digest(p),bytes=p.stat().st_size))
    entries.sort(key=lambda x:x['path'])
    obj=dict(files=entries);obj['source_id']='sha256:'+hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
    (r/'SOURCE_MANIFEST.json').write_text(json.dumps(obj));return obj
class PublicSetupTests(unittest.TestCase):
    def test_manifest_and_tamper(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);fixture(r);setup.validate_manifest(r)
            (r/'lean-toolchain').write_text('different')
            with self.assertRaisesRegex(ValueError,'mismatch'):setup.validate_manifest(r)
    def test_manifest_identity_is_recomputed(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);obj=fixture(r);obj['source_id']='sha256:'+'0'*64;(r/'SOURCE_MANIFEST.json').write_text(json.dumps(obj))
            with self.assertRaisesRegex(ValueError,'digest mismatch'):setup.validate_manifest(r)
    def test_symlink_input_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);fixture(r);p=r/'lean-toolchain';p.unlink();p.symlink_to(r/'lakefile.lean')
            with self.assertRaisesRegex(ValueError,'nonregular'):setup.validate_manifest(r)
    def test_initial_project_objects_refused(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);setup.require_clean_project(r);(r/'Proof.olean').write_text('object')
            with self.assertRaisesRegex(ValueError,'Lean objects'):setup.require_clean_project(r)
    def test_environment_does_not_inherit_lean_or_python_paths(self):
        with patch.dict(os.environ,{'LEAN_PATH':'private','PYTHONPATH':'private','LEAN_SRC_PATH':'private','LAKE_HOME':'private','ELAN_TOOLCHAIN':'other'}):
            e=setup.clean_environment()
            for key in ['LEAN_PATH','PYTHONPATH','LEAN_SRC_PATH','LAKE_HOME','ELAN_TOOLCHAIN']:self.assertNotIn(key,e)

    def test_full_cache_scope_includes_library_smoke_and_cases(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d)
            for rel,text in [('LeanPEP/X.lean','import Mathlib.Analysis.Convex.Function\n'),('tests/lean/smoke/X.lean','import Mathlib.Tactic\n'),('data/cases/pg/X.lean','import Mathlib.Data.Matrix.Mul\n'),('data/paper/old/Replay.lean','import Mathlib\n')]:
                p=r/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
            self.assertEqual(set(setup.mathlib_imports(r)),{'Mathlib.Analysis.Convex.Function','Mathlib.Tactic','Mathlib.Data.Matrix.Mul'})
