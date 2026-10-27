"""GD2 real-source coverage and fail-closed regressions; old routes stay separate."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import replay_structured_gd_two as gd

ARCHIVE=Path(__file__).resolve().parents[2]/'data/fixtures/pepit_capture/gd_two_live_clarabel_20260930.json'

class StructuredGDTwoTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.c=json.loads(ARCHIVE.read_bytes());cls.u,cls.a,cls.g=gd.generate(cls.c)

    def test_real_positive_complete_policy(self):
        self.assertTrue(self.c['producer']['live_capture_performed'])
        self.assertEqual(self.c['steps'],2)
        self.assertTrue(self.a['accepted']);self.assertEqual(self.a['coefficient_count'],53)
        self.assertEqual(self.u.bound,Q(50000,499999))
        self.assertEqual(len(self.u.assumption_terms),14)
        self.assertEqual(len(self.u.dual_matrix),4)
        self.assertTrue(self.g['residual_recomputed'])

    def test_second_step_target_reference_and_source_rejected(self):
        mutations=[lambda c:c.__setitem__('steps',1),
            lambda c:c['profile'].__setitem__('step_size','1/2'),
            lambda c:c['profile'].__setitem__('target','f1-f_star'),
            lambda c:c['samples'][3]['position'][2].__setitem__('num',0),
            lambda c:c['samples'][3]['gradient'][3].__setitem__('num',0),
            lambda c:c['reference']['gradient'].__setitem__(0,'1'),
            lambda c:c['samples'][0]['position'][0].__setitem__('num',1),
            lambda c:c['constraints'].reverse(),
            lambda c:c['constraints'][0]['expression']['value_coeff'][4].__setitem__('num',-1),
            lambda c:c['constraints'][2]['expression']['gram_coeff'][0][1].__setitem__('num',-2)]
        for k,mutate in enumerate(mutations):
            c=copy.deepcopy(self.c);mutate(c)
            with self.subTest(mutation=k),self.assertRaises(ValueError):gd.parse(c)

    def test_raw_shapes_and_ordered_candidate_references_rejected(self):
        for mutate in [lambda c:c['numerical']['multipliers'].pop(),lambda c:c['numerical']['residual'][3].pop(),lambda c:c['numerical'].__setitem__('bound',0.1)]:
            c=copy.deepcopy(self.c);mutate(c)
            with self.assertRaises(ValueError):gd.parse(c)
        ts=list(self.u.assumption_terms);ts[2]=replace(ts[2],index=3)
        with self.assertRaises(ValueError):gd.audit(self.c,replace(self.u,assumption_terms=tuple(ts)))

    def test_nonzero_matrix_and_factor_corruption_rejected(self):
        m=[list(r) for r in self.u.dual_matrix];m[2][2]+=Q(1,1000000)
        self.assertFalse(gd.audit(self.c,replace(self.u,dual_matrix=tuple(map(tuple,m))))['accepted'])
        fs=list(self.u.dual_factor.factors);fs[0]=replace(fs[0],weight=fs[0].weight+1)
        self.assertFalse(gd.audit(self.c,replace(self.u,dual_factor=replace(self.u.dual_factor,factors=tuple(fs))))['accepted'])

    def test_mathematically_valid_outside_budget_and_bypass_rejected(self):
        e=Q(1,1000);m=[list(r) for r in self.u.dual_matrix];m[0][0]+=e
        ts=list(self.u.assumption_terms);ts[1]=replace(ts[1],weight=ts[1].weight+e)
        f=gd.gram.RankOneFactorSpec(e,(Q(1),Q(0),Q(0),Q(0)))
        u=replace(self.u,bound=self.u.bound+e,assumption_terms=tuple(ts),dual_matrix=tuple(map(tuple,m)),dual_factor=replace(self.u.dual_factor,factors=self.u.dual_factor.factors+(f,)))
        a=gd.audit(self.c,u);self.assertTrue(a['original_upper_mirror']['accepted']);self.assertFalse(a['accepted'])
        c=copy.deepcopy(self.c);c['policy']['max_abs_error']='0.01'
        with self.assertRaises(ValueError):gd.audit(c,u)

    def test_lean_failure_never_publishes(self):
        with tempfile.TemporaryDirectory() as temp:
            d=Path(temp)/'out'
            with patch.object(gd,'check_lean',return_value=dict(checked=False,reason='injected_failure',replay_exit=1)):
                with self.assertRaisesRegex(ValueError,'Lean did not accept'):gd.run(ARCHIVE,d,'LeanPEP.Imported.GDTwoFailure')
            self.assertFalse((d/'selected_exact.json').exists())
            r=json.loads((d/'report.json').read_text());self.assertFalse(r['actual_upper_verified']);self.assertIsNone(r['selected_endpoint'])

    def test_same_archive_determinism(self):
        u,a,g=gd.generate(json.loads(ARCHIVE.read_bytes()))
        self.assertEqual((u,a,g),(self.u,self.a,self.g))
        x=gd.render(self.c,u,'LeanPEP.Imported.GDTwoA');y=gd.render(self.c,u,'LeanPEP.Imported.GDTwoB')
        self.assertEqual(x.replace('GDTwoA','GDTwoB'),y)

if __name__=='__main__':unittest.main()
