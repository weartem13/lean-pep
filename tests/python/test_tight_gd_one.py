from pathlib import Path
from dataclasses import replace
from fractions import Fraction as Q
from unittest import mock
from types import SimpleNamespace
import unittest,copy,tempfile,json
import replay_tight_gd_one as t
import capture_tight_gd_one as capture

class TightGDTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cp=t.ROOT/'data/cases/gd/one-step-exact/capture.json';cls.sp=cls.cp.parent/'primal_observation.json'
        cls.c,cls.s,cls.raw=t.verify_live_archive(cls.cp,cls.sp)
        cls.d,cls.a,cls.g=t.exact_primal(cls.c,cls.s,cls.raw)
        cls.oldc,cls.olds,cls.oldraw=t.read_pair(t.ROOT/'data/cases/gd/one-step-gap/capture.json',t.ROOT/'data/cases/gd/one-step-gap/primal_observation.json')
    def test_new_positive_all13_and_exact_optimum(self):
        self.assertTrue(self.a['candidate_diagnostic_accepted']);self.assertEqual(self.a['beta'],Q(1,6));self.assertEqual(self.a['policy']['count'],13)
        self.assertEqual(len(self.a['full_native_rows_geZero']),11);self.assertEqual(len(self.a['canonical_interpolation_slacks']),9)
    def test_old_optimal_face_budget_rejected(self):
        d,a,g=t.exact_primal(self.oldc,self.olds,self.oldraw)
        self.assertFalse(a['policy']['accepted']);self.assertGreater(abs(self.oldraw.G[0][2]-Q(1,3)),t.ETA)
    def test_dual_exact32_source_and_psd(self):
        u,a,g=t.exact_dual(self.oldc);self.assertEqual(u.bound,Q(1,6));self.assertEqual(g['a'],Q(8529,24767));self.assertTrue(a['accepted']);self.assertEqual(a['coefficient_count'],32)
        self.assertFalse(t.dual.audit(self.oldc,replace(u,bound=Q(1,7)))['accepted'])
    def test_sources_cannot_be_mixed(self):
        with self.assertRaises(ValueError):t.validate(self.c,self.olds)
        with self.assertRaises(ValueError):t.validate(self.oldc,self.s)
    def test_symbolic_mutations_and_omitted_row(self):
        changes=[lambda c:c.update(steps=2),lambda c:c.update(algorithm='proximal_gradient'),lambda c:c['constraints'].pop(),lambda c:c['objective']['value_coeff'].__setitem__(3,{'num':0,'den':1})]
        for change in changes:
            c=copy.deepcopy(self.c);change(c)
            with self.assertRaises(ValueError):t.audit(c,self.s,self.raw,self.d)
    def test_gram_value_and_psd_mutations(self):
        G=[list(r) for r in self.d.G];G[0][1]+=Q(1,10**7)
        self.assertFalse(t.audit(self.c,self.s,self.raw,replace(self.d,G=tuple(map(tuple,G))))['native_psd'])
        F=list(self.d.F);F[2]+=t.ETA
        self.assertFalse(t.audit(self.c,self.s,self.raw,replace(self.d,F=tuple(F)))['candidate_diagnostic_accepted'])
    def test_feasible_gauge_outside_budget(self):
        d=replace(self.d,F=tuple(v+Q(1,1000) if i<3 else v for i,v in enumerate(self.d.F)))
        a=t.audit(self.c,self.s,self.raw,d);self.assertTrue(a['native_psd']);self.assertTrue(all(v<=0 for v in a['native_rows_leZero']));self.assertFalse(a['policy']['accepted'])
    def test_offline_reproducibility(self):
        self.assertEqual(t.exact_primal(*t.read_pair(self.cp,self.sp)),(self.d,self.a,self.g))
        self.assertEqual((t.ROOT/'data/cases/gd/one-step-exact/selected_primal.json').read_bytes(),(t.ROOT/'data/cases/gd/one-step-exact/replay-check/selected_primal.json').read_bytes())
    def test_provenance_options_tamper(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            for name in ['capture.json','primal_observation.json','environment.json','provenance.json']:(d/name).write_bytes((self.cp.parent/name).read_bytes())
            e=json.loads((d/'environment.json').read_text());e['effective_solver_options']['max_iter']=300;(d/'environment.json').write_text(json.dumps(e))
            with self.assertRaises(ValueError):t.verify_live_archive(d/'capture.json',d/'primal_observation.json')
    def test_observer_passes_and_records_effective_kwargs(self):
        # Test double only: no solve. Actual source evidence is live_001.log.
        import numpy as np
        from PEPit import PEP
        called=[]
        problem=SimpleNamespace(wrapper=SimpleNamespace(get_primal_variables=lambda:(np.eye(3),np.zeros(4))))
        def fake_solve(problem,*args,**kwargs):called.append(kwargs);return 0
        def fake_capture():
            PEP.solve(problem,wrapper='cvxpy',solver='CLARABEL',tol_feas=1e-10,max_iter=300)
            return copy.deepcopy(self.c)
        with mock.patch.object(PEP,'solve',fake_solve),mock.patch.object(capture.original,'capture',fake_capture):c,s,p=capture.capture_pair(capture.OPTIONS)
        self.assertEqual(len(called),1)
        for k,v in capture.OPTIONS.items():self.assertEqual(called[0][k],v);self.assertEqual(p['effective_solve_kwargs'][k],v)
        self.assertEqual(c['producer']['options'],capture.OPTIONS)
    def test_lean_failure_no_selected(self):
        with tempfile.TemporaryDirectory(dir=t.ROOT) as tmp:
            for kind in ['dual','primal']:
                out=Path(tmp)/kind
                def fail(cmd,log):log.write_text('Test double: Lean failure, not proof evidence.');return dict(exit=1)
                with mock.patch.object(t,'invoke',side_effect=fail):rc=t.run(kind,t.ROOT/'data/cases/gd/one-step-gap/capture.json' if kind=='dual' else self.cp,self.sp,out,'LeanPEP.Imported.TestFail')
                self.assertEqual(rc,2);self.assertFalse(list(out.glob('selected*')))
if __name__=='__main__':unittest.main()
