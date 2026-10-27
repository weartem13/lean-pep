"""PG1 archived native primal boundary; mocks only test fail-closed publishing."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import import_pepit_proximal_gradient_capture as cap
import replay_primal_pg_one as p
import synthesize_psd_factors as psd

class PGOnePrimalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cp=p.ROOT/'data/cases/pg/one-step-exact/capture.json';cls.sp=p.ROOT/'data/cases/pg/one-step-exact/primal_observation.json'
        cls.c,cls.s,cls.raw=p.read_inputs(cls.cp,cls.sp);cls.d=p.generate(cls.raw)

    def test_real_positive_full_coverage(self):
        a=p.audit(self.c,self.s,self.raw,self.d)
        self.assertTrue(a['candidate_diagnostic_accepted'])
        self.assertEqual((len(a['full_rows_leZero']),len(a['canonical_rows_geZero'])),(15,14))
        self.assertEqual(a['policy']['count'],42);self.assertEqual(a['beta'],Q(1,4));self.assertEqual(a['tau'],a['beta'])
        self.assertNotEqual(self.d.G[1][1],0)

    def test_raw_exact_rejection(self):
        a=p.raw_diagnosis(self.c,self.raw)
        self.assertEqual(a['first_value'],Q(53729274623,2000000000000000000000000))
        self.assertEqual(a['first_nonpositive_pivot'],4)
        self.assertLess(a['unpermuted_ldl_pivots'][4],0)
        self.assertTrue(a['exact_witness_verified'])
        self.assertFalse(p.audit(self.c,self.s,self.raw,self.raw)['candidate_diagnostic_accepted'])

    def test_source_sample_origin_oracle_mutations(self):
        mutators=[lambda d:d['constraints'][1]['expression'].update(const=dict(num=-2,den=1)),
                  lambda d:d['smooth_samples'][0].update(value_index=2),
                  lambda d:d['smooth_samples'][0].update(position=[dict(num=0,den=1)]*6),
                  lambda d:d['nonsmooth_samples'][0].update(oracle=[dict(num=0,den=1)]*6)]
        for change in mutators:
            d=copy.deepcopy(self.c.capture);change(d)
            with self.subTest(change=change),self.assertRaises(ValueError):
                c=cap.convert(d,1);p.audit(c,self.s,self.raw,self.d)

    def test_primal_roles_order_and_origin(self):
        for key,value in [('basis_order',list(reversed(self.s['basis_order']))),('value_order',list(reversed(p.VALUES))),('tau_index',0),('point_eval_used',True),('capture_sha256','0'*64)]:
            s=copy.deepcopy(self.s);s[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):p.audit(self.c,s,self.raw,self.d)

    def test_single_axis_and_factor_corruption(self):
        G=[list(r) for r in self.d.G];G[0][1]+=Q(1,10**7)
        a=p.audit(self.c,self.s,self.raw,replace(self.d,G=tuple(map(tuple,G))))
        self.assertFalse(a['native_psd']);self.assertFalse(a['candidate_diagnostic_accepted'])
        f=psd.synthesize_psd(self.d.G);bad=replace(f,factors=(replace(f.factors[0],weight=f.factors[0].weight+1),)+f.factors[1:])
        self.assertFalse(p.audit(self.c,self.s,self.raw,self.d,bad)['native_psd'])

    def test_nonactive_row_cannot_be_omitted_or_violated(self):
        self.assertLess(p.eval_expr(self.c.captured_rows[9],self.d),0)
        capture=copy.deepcopy(self.c.capture);del capture['constraints'][9]
        with self.assertRaises(ValueError):cap.convert(capture,1)
        V=list(self.d.F);V[1]+=1;V[3]-=1
        bad=replace(self.d,F=tuple(V));a=p.audit(self.c,self.s,self.raw,bad)
        self.assertGreater(a['native_rows_leZero'][9],0);self.assertFalse(a['candidate_diagnostic_accepted'])

    def test_tau_direction_and_objective(self):
        V=list(self.d.F);V[5]+=Q(1,10**7)
        a=p.audit(self.c,self.s,self.raw,replace(self.d,F=tuple(V)))
        self.assertGreater(a['native_rows_leZero'][0],0);self.assertFalse(a['candidate_diagnostic_accepted'])
        V[5]=self.d.F[5]-Q(1,10**6)
        a=p.audit(self.c,self.s,self.raw,replace(self.d,F=tuple(V)))
        self.assertTrue(a['candidate_diagnostic_accepted']);self.assertLess(a['tau'],a['beta'])
        capture=copy.deepcopy(self.c.capture);capture['metric']['value_coeff'][4]=dict(num=-1,den=1)
        with self.assertRaises(ValueError):p.audit(cap.convert(capture,1),self.s,self.raw,self.d)

    def test_feasible_but_outside_budget(self):
        d=replace(self.d,F=tuple(x+Q(1,1000) if i<5 else x for i,x in enumerate(self.d.F)))
        a=p.audit(self.c,self.s,self.raw,d)
        self.assertTrue(a['native_psd']);self.assertTrue(all(x<=0 for x in a['native_rows_leZero']))
        self.assertTrue(all(x>=0 for x in a['canonical_rows_geZero']))
        self.assertFalse(a['policy']['accepted']);self.assertFalse(a['candidate_diagnostic_accepted'])

    def test_lean_failure_never_publishes(self):
        with tempfile.TemporaryDirectory(dir=p.ROOT) as tmp:
            out=Path(tmp)/'run'
            def failed(cmd,log):log.write_text('simulated process failure (not Lean evidence)\n');return 1
            with mock.patch.object(p.pipeline,'invoke',side_effect=failed):report,rc=p.run(self.cp,self.sp,out,'LeanPEP.Imported.PrimalFailureTest')
            self.assertEqual(rc,2);self.assertFalse(report['finite_primal_verified']);self.assertFalse((out/'selected_primal.json').exists())

    def test_deterministic_from_same_bytes(self):
        c,s,raw=p.read_inputs(self.cp,self.sp)
        self.assertEqual(p.generate(raw),self.d)
        self.assertEqual(p.audit(c,s,raw,p.generate(raw)),p.audit(self.c,self.s,self.raw,self.d))

    def test_axioms_gate_requires_actual_primal_names(self):
        self.assertFalse(p.axioms_ok("'LeanPEP.Imported.Fake.actual_upper' depends on axioms: [propext]",'LeanPEP.Imported.Fake'))
        self.assertFalse(p.axioms_ok('sorryAx','LeanPEP.Imported.Fake'))

if __name__=='__main__':unittest.main()
