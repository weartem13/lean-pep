"""GD1 native finite primal regressions; mock is only a failure-publication test."""
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
from unittest import mock
import unittest,copy,tempfile
import replay_primal_gd_one as p
import synthesize_psd_factors as psd

class GDOnePrimalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cp=p.ROOT/'data/cases/gd/one-step-gap/capture.json';cls.sp=p.ROOT/'data/cases/gd/one-step-gap/primal_observation.json'
        cls.c,cls.s,cls.raw=p.read_inputs(cls.cp,cls.sp);cls.d,cls.a,cls.trials=p.generate(cls.c,cls.s,cls.raw)

    def test_positive_real_candidate_all_obligations(self):
        self.assertTrue(self.a['candidate_diagnostic_accepted']);self.assertEqual(len(self.a['canonical_interpolation_slacks']),9)
        self.assertEqual(len(self.a['full_native_rows_geZero']),11);self.assertEqual(self.a['policy']['count'],13)
        self.assertGreater(self.a['beta'],0);self.assertTrue(all(x>=0 for x in self.a['canonical_interpolation_slacks']))

    def test_raw_psd_but_scalar_infeasible(self):
        a=p.audit(self.c,self.s,self.raw,self.raw)
        self.assertTrue(a['native_psd']);self.assertEqual(a['native_rows_leZero'][0],Q(1260613,10**18))
        self.assertTrue(any(x<0 for x in a['canonical_interpolation_slacks']));self.assertFalse(a['candidate_diagnostic_accepted'])

    def test_bounded_trials_preserve_first_failures(self):
        self.assertEqual(len(self.trials),6);self.assertFalse(self.trials[0]['native_psd'])
        self.assertEqual(self.trials[0]['rows'][0],Q(1,10**6));self.assertTrue(self.trials[-1]['accepted'])
        self.assertTrue(all(t['first_failure'] is not None for t in self.trials[:-1]))

    def test_source_model_roles_reference_and_endpoint(self):
        changes=[lambda c:c['reference']['gradient'].__setitem__(0,'1'),lambda c:c['profile'].update(step_size='2'),lambda c:c['samples'][2].update(position=c['samples'][1]['position']),lambda c:c['samples'][2].update(gradient=c['samples'][1]['gradient']),lambda c:c['samples'][0].update(value_index=1),lambda c:c['basis_order'].reverse(),lambda c:c['value_order'].reverse(),lambda c:c['constraints'][1]['expression'].update(const={'num':-2,'den':1})]
        for mutate in changes:
            c=copy.deepcopy(self.c);mutate(c)
            with self.subTest(mutate=mutate),self.assertRaises(ValueError):p.audit(c,self.s,self.raw,self.d)

    def test_sidecar_roles_and_source_hash(self):
        for key,value in [('tau_index',0),('value_order',['tau','f_star','f0','f1']),('capture_sha256','0'*64),('point_eval_used',True),('projection_performed_by_exporter',True)]:
            s=copy.deepcopy(self.s);s[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):p.audit(self.c,s,self.raw,self.d)

    def test_single_axis_and_factor_rejected(self):
        G=[list(r) for r in self.d.G];G[1][2]+=Q(1,10**7)
        self.assertFalse(p.audit(self.c,self.s,self.raw,replace(self.d,G=tuple(map(tuple,G))))['native_psd'])
        f=psd.synthesize_psd(self.d.G);bad=replace(f,factors=(replace(f.factors[0],weight=f.factors[0].weight+1),)+f.factors[1:])
        self.assertFalse(p.audit(self.c,self.s,self.raw,self.d,bad)['native_psd'])

    def test_radius_only_is_not_gd_finite_feasible(self):
        F=list(self.d.F);F[2]+=Q(1,1000000)
        a=p.audit(self.c,self.s,self.raw,replace(self.d,F=tuple(F)))
        self.assertTrue(a['native_psd']);self.assertGreaterEqual(a['radius_slack'],0)
        self.assertTrue(any(x<0 for x in a['canonical_interpolation_slacks']));self.assertFalse(a['candidate_diagnostic_accepted'])

    def test_nonactive_interpolation_cannot_be_omitted(self):
        i=4;self.assertLess(self.a['native_rows_leZero'][i],0)
        c=copy.deepcopy(self.c);del c['constraints'][i]
        with self.assertRaises(ValueError):p.audit(c,self.s,self.raw,self.d)
        c=copy.deepcopy(self.c);c['constraints'][i]['expression']['value_coeff']=[{'num':0,'den':1}]*4
        with self.assertRaises(ValueError):p.audit(c,self.s,self.raw,self.d)

    def test_tau_direction_actual_renderer_values_and_metric(self):
        F=list(self.d.F);F[3]+=Q(1,1000000)
        self.assertFalse(p.audit(self.c,self.s,self.raw,replace(self.d,F=tuple(F)))['candidate_diagnostic_accepted'])
        F[3]=Q(83333,500001);d=replace(self.d,F=tuple(F));a=p.audit(self.c,self.s,self.raw,d)
        self.assertTrue(a['candidate_diagnostic_accepted']);self.assertLess(a['tau'],a['beta'])
        rendered=p.render(self.c,self.s,self.raw,d,'LeanPEP.Imported.GDPrimalRenderTest')
        self.assertIn(p.gram.lean_rat(F[3]),rendered)
        self.assertIn(p.gram.lean_rat(a['beta']),rendered) # render-only, not a claim of another Lean run
        c=copy.deepcopy(self.c);c['metric']['value_coeff'][2]={'num':-1,'den':1}
        with self.assertRaises(ValueError):p.audit(c,self.s,self.raw,self.d)

    def test_mathematically_feasible_but_policy_rejected(self):
        d=replace(self.d,F=tuple(v+Q(1,1000) if i<3 else v for i,v in enumerate(self.d.F)))
        a=p.audit(self.c,self.s,self.raw,d)
        self.assertTrue(a['native_psd']);self.assertTrue(all(x<=0 for x in a['native_rows_leZero']))
        self.assertTrue(all(x>=0 for x in a['canonical_interpolation_slacks']));self.assertFalse(a['policy']['accepted'])
        self.assertFalse(a['candidate_diagnostic_accepted'])

    def test_failure_does_not_publish_and_axioms_fail_closed(self):
        with tempfile.TemporaryDirectory(dir=p.ROOT) as tmp:
            out=Path(tmp)/'run'
            def failed(cmd,log):log.write_text('Simulated failure; not Lean evidence.\n');return 1
            with mock.patch.object(p.pipeline,'invoke',side_effect=failed):r,rc=p.run(self.cp,self.sp,out,'LeanPEP.Imported.GDPrimalFail')
            self.assertEqual(rc,2);self.assertFalse(r['finite_primal_verified']);self.assertFalse((out/'selected_primal.json').exists())
        self.assertFalse(p.axioms_ok("'X.actual_upper' depends on axioms: [propext]",'X'))

    def test_independent_determinism(self):
        c,s,raw=p.read_inputs(self.cp,self.sp)
        self.assertEqual(p.generate(c,s,raw),(self.d,self.a,self.trials))

if __name__=='__main__':unittest.main()
