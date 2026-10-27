import unittest,tempfile,json,sys,time
from pathlib import Path
from tests.support.refinement.run_batch import numerical_key,source_key,guarded_run,classify,write
class HarnessTests(unittest.TestCase):
 def fixture(self):return dict(numerical=dict(bound='0.25',multipliers=['0.0','1.0'],residual=[['0.5']]),basis_order=['x'],constraints=[{'label':'radius'}],producer={'status':'ok'})
 def test_fraction_dedup_ignores_spelling(self):
  a=self.fixture();b=self.fixture();b['numerical']['bound']='0.250000';b['producer']['status']='other';self.assertEqual(numerical_key(a),numerical_key(b))
 def test_full_matrix_and_zero_weights_count(self):
  a=self.fixture();b=self.fixture();b['numerical']['residual'][0][0]='0.50000001';self.assertNotEqual(numerical_key(a),numerical_key(b));b=self.fixture();b['numerical']['multipliers'][0]='0.000001';self.assertNotEqual(numerical_key(a),numerical_key(b))
 def test_source_mismatch_separate_from_numerics(self):
  a=self.fixture();b=self.fixture();b['basis_order']=['wrong'];self.assertEqual(numerical_key(a),numerical_key(b));self.assertNotEqual(source_key(a),source_key(b))
 def test_unknown_not_fabricated(self):
  with tempfile.TemporaryDirectory() as x:
   p=Path(x);r=classify(p,p/'absent.json');self.assertFalse(r['consumer_result']['actual_upper_verified']);self.assertEqual(r['counts']['grids_observed'],0)
 def test_exit_propagated(self):
  with tempfile.TemporaryDirectory() as x:
   p=Path(x);r=guarded_run([sys.executable,'-c','raise SystemExit(7)'],p,p/'run.log',5);self.assertEqual(r['exit'],7)
 def test_wall_limit(self):
  with tempfile.TemporaryDirectory() as x:
   p=Path(x);r=guarded_run([sys.executable,'-c','import time; time.sleep(5)'],p,p/'run.log',.2);self.assertEqual(r['exit'],124);self.assertLess(r['wall_seconds'],3)
if __name__=='__main__':unittest.main()
