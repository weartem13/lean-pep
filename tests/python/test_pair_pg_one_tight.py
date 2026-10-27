"""Exact accepted-proof retention; mathematical rejection lives in Regression.lean."""
from pathlib import Path
import tempfile,unittest
import pair_pg_one_tight as p

class PGOnePairTests(unittest.TestCase):
    def test_accepted_pair_and_all_inputs(self):
        self.assertEqual(p.validate(p.ROOT),p.INPUTS)

    def test_only_namespace_and_autoimplicit_change(self):
        for path,old,new in p.COPIES:
            src=(p.ROOT/path).read_text();copy=(p.ROOT/('LeanPEP/Imported/'+new.rsplit('.',1)[-1]+'.lean')).read_text()
            self.assertEqual(copy,p.renamed(src,old,new))
            self.assertEqual(copy.replace('\nset_option autoImplicit false','',1).replace(new,old),src)

    def test_each_accepted_input_tamper_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for f in p.INPUTS:
                dest=root/f;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((p.ROOT/f).read_bytes())
            for f in p.INPUTS:
                dest=root/f;before=dest.read_bytes();dest.write_bytes(before+b'\n')
                with self.subTest(path=f),self.assertRaisesRegex(ValueError,'accepted input changed'):p.validate(root)
                dest.write_bytes(before)

    def test_new_copies_and_no_overwrite(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp);result=p.materialize(p.ROOT,out)
            self.assertFalse(result['numerical_recovery']);self.assertEqual(result['solver_calls'],0)
            with self.assertRaisesRegex(ValueError,'overwrite'):p.materialize(p.ROOT,out)

if __name__=='__main__':unittest.main()
