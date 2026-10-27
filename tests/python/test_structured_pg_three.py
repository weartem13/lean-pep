"""Real T=3 archive regression; Python diagnostics are not Lean evidence."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import prepare_proximal_gradient_candidates as prep
import replay_structured_pg_three as structured

ROOT=Path(__file__).resolve().parents[2]
ARCHIVE=ROOT/'data/fixtures/pepit_capture/pg_three_live_clarabel_20261003.json'
NS='LeanPEP.Imported.Test.StructuredThree'


class StructuredPGThreeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original,cls.c=structured.read_archive(ARCHIVE)
        cls.a,cls.audit,cls.generation=structured.build_candidate(cls.c)

    def test_real_positive_and_three_step_statement(self):
        self.assertTrue(self.audit['candidate_diagnostic_accepted'])
        self.assertEqual(self.a.upper.bound,Q(41630,499559))
        self.assertEqual(self.audit['coefficient_count'],246)
        self.assertEqual(self.generation['factor_count'],8)
        self.assertEqual(self.generation['trial_count'],442)
        self.assertEqual(prep.source_tree(self.a),prep.source_tree(self.c.prepared.raw.artifact))
        self.assertEqual(ARCHIVE.read_bytes(),self.original)
        self.assertEqual([t.index for t in self.a.upper.assumption_terms],list(range(34)))
        self.assertEqual(self.a.upper.interp_terms,())
        text=structured.render_replay(self.c,self.a,NS)
        theorem=text.split('theorem actual_upper',1)[1]
        self.assertIn('IsSmoothProxRun 3 L h g x',theorem)
        self.assertIn('f (x 3) + h (x 3)',theorem)
        self.assertNotIn('f (x 1)',theorem)
        self.assertIn('SourceQ 2 34',text)

    def test_wrong_horizon_and_intermediate_objective_rejected(self):
        wrong=copy.deepcopy(self.c.capture);wrong['horizon']=1
        with self.assertRaises(ValueError):
            structured.build_candidate(cap.convert(wrong,3))
        wrong=copy.deepcopy(self.c.capture)
        values=wrong['value_order'];coeffs=wrong['metric']['value_coeff']
        for old,new in [('f3','f2'),('h3','h2')]:
            coeffs[values.index(old)]=dict(num=0,den=1)
            coeffs[values.index(new)]=dict(num=1,den=1)
        with self.assertRaises(ValueError):
            structured.build_candidate(cap.convert(wrong,3))

    def test_source_and_reference_mutations_rejected(self):
        wrong=copy.deepcopy(self.c.capture)
        wrong['constraints'][1]['expression']['const']=dict(num=-2,den=1)
        with self.assertRaises(ValueError):
            structured.build_candidate(cap.convert(wrong,3))
        terms=list(self.a.upper.assumption_terms)
        terms[2]=replace(terms[2],index=3)
        bad=replace(self.a,upper=replace(self.a.upper,assumption_terms=tuple(terms)))
        audit=structured.audit_candidate(self.c,bad)
        self.assertFalse(audit['policy_checks']['assumption_references'])
        self.assertFalse(audit['candidate_diagnostic_accepted'])

    def test_both_gram_axes_are_checked(self):
        S=[list(row) for row in self.a.upper.dual_matrix]
        S[0][3]+=Q(1,10**7)
        bad=replace(self.a,upper=replace(self.a.upper,dual_matrix=tuple(map(tuple,S))))
        audit=structured.audit_candidate(self.c,bad)
        self.assertFalse(audit['structured_diagnostic']['compact_certificate']['symmetric'])
        self.assertFalse(audit['candidate_diagnostic_accepted'])
        with self.assertRaisesRegex(ValueError,'candidate rejected'):
            structured.render_replay(self.c,bad,NS)

    def test_valid_looser_upper_cannot_bypass_raw_budget(self):
        a=self.a;delta=Q(1,1000);v=(Q(1),Q(0),Q(-1),Q(0),Q(0),Q(0),Q(0),Q(0),Q(0),Q(0))
        ts=list(a.upper.assumption_terms);ts[1]=replace(ts[1],weight=ts[1].weight+delta)
        S=tuple(tuple(a.upper.dual_matrix[i][j]+delta*v[i]*v[j] for j in range(10)) for i in range(10))
        fac=gram.FactorCertSpec(a.upper.dual_factor.factors+(gram.RankOneFactorSpec(delta,v),))
        bad=replace(a,upper=replace(a.upper,bound=a.upper.bound+delta,assumption_terms=tuple(ts),dual_matrix=S,dual_factor=fac))
        audit=structured.audit_candidate(self.c,bad)
        self.assertTrue(audit['structured_diagnostic']['diagnostic_passed'])
        self.assertFalse(audit['policy_checks']['error_bounds'])
        self.assertFalse(audit['candidate_diagnostic_accepted'])
        policy=replace(self.c.prepared.policy,max_abs_error=Q(1))
        wrong=replace(self.c,prepared=replace(self.c.prepared,policy=policy))
        with self.assertRaisesRegex(ValueError,'M/eta'):
            structured.audit_candidate(wrong,bad)

    def test_lean_failure_cannot_publish_selected_or_actual_upper(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'fresh'
            with mock.patch.object(structured.pipeline,'check_lean',return_value={'checked':False}), \
                 mock.patch.object(structured.pipeline,'invoke',return_value=0):
                report,code=structured.run(ARCHIVE,out,NS)
            self.assertEqual(code,3)
            self.assertFalse(report['actual_upper_verified'])
            self.assertFalse(report['candidate_accepted'])
            self.assertFalse((out/'selected_exact.json').exists())
            with self.assertRaisesRegex(ValueError,'new or empty'):
                structured.run(ARCHIVE,out,NS)

    def test_same_archive_reproduces_exact_payload(self):
        _,again=structured.read_archive(ARCHIVE)
        candidate,audit,generation=structured.build_candidate(again)
        self.assertEqual(candidate.upper,self.a.upper)
        self.assertEqual(prep.source_tree(candidate),prep.source_tree(self.a))
        self.assertEqual(generation,self.generation)
        self.assertTrue(audit['candidate_diagnostic_accepted'])

    def test_third_step_nonzero_reference_origin_and_components(self):
        self.assertEqual(self.c.capture['smooth_samples'][0]['oracle'][1],dict(num=1,den=1))
        self.assertEqual(self.c.capture['nonsmooth_samples'][0]['oracle'][1],dict(num=-1,den=1))
        mutations=[lambda c:c['smooth_samples'][4]['position'][7].__setitem__('num',0),
            lambda c:c['smooth_samples'][0]['oracle'][1].__setitem__('num',0),
            lambda c:c['nonsmooth_samples'][0]['oracle'][1].__setitem__('num',0),
            lambda c:c['smooth_samples'][0]['position'][0].__setitem__('num',0),
            lambda c:c['nonsmooth_samples'][0].__setitem__('value_index',0)]
        for i,mutate in enumerate(mutations):
            wrong=copy.deepcopy(self.c.capture);mutate(wrong)
            with self.subTest(mutation=i),self.assertRaises(ValueError):
                structured.build_candidate(cap.convert(wrong,3))
        factors=list(self.a.upper.dual_factor.factors)
        factors[0]=replace(factors[0],weight=factors[0].weight+1)
        bad=replace(self.a,upper=replace(self.a.upper,dual_factor=gram.FactorCertSpec(tuple(factors))))
        self.assertFalse(structured.audit_candidate(self.c,bad)['candidate_diagnostic_accepted'])

    def test_grid_limit_is_not_infeasibility(self):
        with mock.patch.object(structured,'MAX_GRID_TRIALS',0):
            with self.assertRaisesRegex(ValueError,'exhausted; no infeasibility claim'):
                structured.build_candidate(self.c)

if __name__=='__main__':
    unittest.main()
