"""GD(1) archive-specific regression, including failure-to-publish semantics."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import replay_structured_gd_one as gd

ROOT=Path(__file__).resolve().parents[2]
ARCHIVE=ROOT/'data/fixtures/pepit_capture/gd_one_live_clarabel_20260930.json'

class StructuredGDOneTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.capture=json.loads(ARCHIVE.read_bytes());cls.upper,cls.audit,cls.generation=gd.generate(cls.capture)

    def test_real_archive_positive_and_complete_policy(self):
        self.assertTrue(self.capture['producer']['live_capture_performed'])
        self.assertTrue(self.audit['accepted']);self.assertEqual(self.audit['coefficient_count'],32)
        self.assertEqual(self.upper.bound,Q(83333,499997))
        self.assertEqual(len(self.upper.assumption_terms),8)
        self.assertTrue(self.generation['residual_recomputed'])

    def test_profile_and_endpoint_mutations_rejected(self):
        for field,value in [('steps',2),('algorithm','proximal_gradient')]:
            c=copy.deepcopy(self.capture);c[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):gd.parse(c)
        for field,value in [('step_size','1/2'),('target','f0-f_star'),('L','2')]:
            c=copy.deepcopy(self.capture);c['profile'][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):gd.parse(c)

    def test_source_reference_and_tau_mutations_rejected(self):
        for mutate in [lambda c:c['constraints'].reverse(),
            lambda c:c['reference']['gradient'].__setitem__(0,'1'),
            lambda c:c['samples'][0]['position'][0].__setitem__('num',1),
            lambda c:c['constraints'][0]['expression']['value_coeff'][3].__setitem__('num',-1),
            lambda c:c['constraints'][2]['label'].__setitem__(1,2)]:
            c=copy.deepcopy(self.capture);mutate(c)
            with self.assertRaises(ValueError):gd.parse(c)

    def test_raw_shape_and_numerical_type_rejected(self):
        for mutate in [lambda c:c['numerical']['multipliers'].pop(),
            lambda c:c['numerical']['residual'][0].pop(),
            lambda c:c['numerical'].__setitem__('bound',0.1666666667)]:
            c=copy.deepcopy(self.capture);mutate(c)
            with self.assertRaises(ValueError):gd.parse(c)

    def test_matrix_and_factor_corruption_rejected(self):
        m=[list(r) for r in self.upper.dual_matrix];m[1][1]+=Q(1,1000000)
        self.assertFalse(gd.audit(self.capture,replace(self.upper,dual_matrix=tuple(map(tuple,m))))['accepted'])
        f=list(self.upper.dual_factor.factors);f[0]=replace(f[0],weight=f[0].weight+1)
        self.assertFalse(gd.audit(self.capture,replace(self.upper,dual_factor=replace(self.upper.dual_factor,factors=tuple(f))))['accepted'])

    def test_valid_upper_outside_budget_rejected(self):
        # Add epsilon to radius multiplier, bound and G00 residual: preserves exact identity/PSD.
        e=Q(1,1000);m=[list(r) for r in self.upper.dual_matrix];m[0][0]+=e
        terms=list(self.upper.assumption_terms);terms[1]=replace(terms[1],weight=terms[1].weight+e)
        factor=gd.gram.RankOneFactorSpec(e,(Q(1),Q(0),Q(0)))
        u=replace(self.upper,bound=self.upper.bound+e,assumption_terms=tuple(terms),dual_matrix=tuple(map(tuple,m)),
            dual_factor=replace(self.upper.dual_factor,factors=self.upper.dual_factor.factors+(factor,)))
        a=gd.audit(self.capture,u)
        self.assertTrue(a['original_upper_mirror']['accepted']);self.assertFalse(a['policy']['error_bounds']);self.assertFalse(a['accepted'])
        c=copy.deepcopy(self.capture);c['policy']['max_abs_error']='0.01'
        with self.assertRaises(ValueError):gd.audit(c,u)

    def test_candidate_ordered_reference_rejected(self):
        ts=list(self.upper.assumption_terms);ts[2]=replace(ts[2],index=3)
        with self.assertRaises(ValueError):gd.audit(self.capture,replace(self.upper,assumption_terms=tuple(ts)))

    def test_lean_failure_never_publishes_selected(self):
        with tempfile.TemporaryDirectory() as temp:
            directory=Path(temp)/'out'
            with patch.object(gd,'check_lean',return_value=dict(checked=False,replay_exit=1,reason='injected_failure')):
                with self.assertRaisesRegex(ValueError,'Lean did not accept'):gd.run(ARCHIVE,directory,'LeanPEP.Imported.GDOneTestFailed')
            self.assertFalse((directory/'selected_exact.json').exists())
            r=json.loads((directory/'report.json').read_text());self.assertFalse(r['actual_upper_verified']);self.assertIsNone(r['selected_endpoint'])

    def test_deterministic_archive_payload(self):
        u,a,g=gd.generate(json.loads(ARCHIVE.read_bytes()))
        self.assertEqual(u,self.upper);self.assertEqual(a,self.audit);self.assertEqual(g,self.generation)
        x=gd.render(self.capture,u,'LeanPEP.Imported.GDOneA');y=gd.render(self.capture,u,'LeanPEP.Imported.GDOneB')
        self.assertEqual(x.replace('LeanPEP.Imported.GDOneA','LeanPEP.Imported.GDOneB'),y)

if __name__=='__main__':unittest.main()
