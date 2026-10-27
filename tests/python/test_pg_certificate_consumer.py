"""Portable PG2 consumer contracts; numerical source acceptance is not a hash whitelist."""
from pathlib import Path
import copy,json,tempfile,unittest,shutil,sys
from unittest import mock
import replay_pg_certificate as consumer
import replay_structured_pg_two as strategy
import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
ROOT=Path(__file__).resolve().parents[2]
INPUT=ROOT/'data/fixtures/pepit_capture/pg_two_live_clarabel_20260930.json'
class ConsumerTests(unittest.TestCase):
    def test_pure_core_closure(self):
        graph=consumer.closure(ROOT)
        self.assertFalse(any('Regression' in m or 'Imported' in m or m=='LeanPEP' for m in graph))
        self.assertNotIn('LeanPEP.GramPEP.UpperCertificateExamples',graph)
        review=json.loads((ROOT/consumer.REVIEW).read_text())
        self.assertEqual(set(graph),set(review['modules']))
    def copy_review_root(self,tmp):
        root=Path(tmp)
        shutil.copytree(ROOT/'LeanPEP',root/'LeanPEP')
        (root/'docs').mkdir();shutil.copyfile(ROOT/consumer.REVIEW,root/consumer.REVIEW)
        return root
    def test_r01_actual_example_path_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.copy_review_root(tmp);p=root/'LeanPEP/ActualFunction/ProximalScaling.lean'
            p.write_text(p.read_text().replace('import LeanPEP.ActualFunction.SmoothScalingCore','import LeanPEP.ActualFunction.OneStepScaling'))
            self.assertIn('LeanPEP.GramPEP.UpperCertificateExamples',consumer.dependency_graph(root))
            with self.assertRaisesRegex(ValueError,'unreviewed.*UpperCertificateExamples'):consumer.closure(root)
    def test_renamed_unreviewed_concrete_certificate_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.copy_review_root(tmp);m='LeanPEP.LibrarySupport'
            shutil.copyfile(ROOT/'LeanPEP/GramPEP/UpperCertificateExamples.lean',root/'LeanPEP/LibrarySupport.lean')
            p=root/(consumer.CORE.replace('.','/')+'.lean');p.write_text('import '+m+'\n'+p.read_text())
            with self.assertRaisesRegex(ValueError,'unreviewed.*LibrarySupport'):consumer.closure(root)
    def test_missing_project_dependency_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.copy_review_root(tmp);(root/'LeanPEP/ActualFunction/SmoothScalingCore.lean').unlink()
            with self.assertRaisesRegex(ValueError,'missing LeanPEP source'):consumer.closure(root)
    def test_reviewed_filename_with_changed_content_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.copy_review_root(tmp);p=root/'LeanPEP/ActualFunction/SmoothScalingCore.lean'
            p.write_text(p.read_text()+'\ndef unreviewedValue : Nat := 42\n')
            with self.assertRaisesRegex(ValueError,'content review stale'):consumer.closure(root)
    def test_optional_resource_unavailable_does_not_change_exit(self):
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(consumer,'peak_rss',return_value=None):
            out=Path(tmp)
            self.assertEqual(consumer.run_command(ROOT,out,'ok',[sys.executable,'-c','pass']),0)
            self.assertEqual(consumer.run_command(ROOT,out,'bad',[sys.executable,'-c','raise SystemExit(3)']),3)
            self.assertIsNone(json.loads((out/'commands.json').read_text())[0]['peak_rss_bytes'])
    def test_capture_semantics_not_byte_whitelist(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'different_serialization.json';p.write_text(json.dumps(gram.load_json(INPUT),separators=(',',':')))
            self.assertNotEqual(consumer.digest(p),strategy.CAPTURE_SHA256)
            c=consumer.read_capture(p);a,audit,_=strategy.build_candidate(c)
            self.assertTrue(audit['candidate_diagnostic_accepted'])
            self.assertIn('import '+consumer.CORE+'\n',consumer.render(c,a,'LeanPEP.Imported.Consumer.Test'))
            with self.assertRaisesRegex(ValueError,'integrity'):consumer.read_capture(p,'0'*64)
    def test_source_mismatch_rejected(self):
        d=copy.deepcopy(gram.load_json(INPUT));d['constraints'][1]['expression']['const']={'num':-2,'den':1}
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'bad.json';p.write_text(json.dumps(d))
            with self.assertRaises(ValueError):consumer.read_capture(p)
    def test_output_guard(self):
        with self.assertRaisesRegex(ValueError,'outside'):consumer.fresh_output(ROOT,ROOT/'bad-output')
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError,'already'):consumer.fresh_output(ROOT,Path(tmp))
    def test_actual_lean_failure_never_selects(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'out'
            with mock.patch.object(consumer,'run_command',return_value=1):
                rc=consumer.main(['recover','--source-root',str(ROOT),'--input',str(INPUT),'--output',str(out)])
            self.assertEqual(rc,1);self.assertFalse((out/'selected_exact.json').exists())
            self.assertTrue(json.loads((out/'result.json').read_text())['inputs_unchanged'])
            self.assertFalse(json.loads((out/'result.json').read_text())['actual_upper_verified'])
            self.assertEqual(json.loads((out/'result.json').read_text())['pure_closure_status'],'passed_content_review')
if __name__=='__main__':unittest.main()
