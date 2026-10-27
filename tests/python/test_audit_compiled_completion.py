"""D12: independent complete coefficient-system and raw-box binding diagnostics."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import audit_compiled_completion as audit
import import_exact_gram_bundle as gram
import solve_exact_linear_system as lin
import solve_exact_box_system as box

ROOT = Path(__file__).resolve().parents[2]


class CompilerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs = {w: gram.load_json(ROOT/f'data/fixtures/pepit_bounded/pg_{w}.json')
                      for w in ('one', 'two', 'three', 'budget')}
        cls.boxed = {w: audit.run(d, 'box') for w, d in cls.inputs.items()}
        cls.badinput = gram.load_json(ROOT/'data/fixtures/pepit_completion/pg_inconsistent.json')
        cls.linear = audit.run(cls.badinput, 'linear')

    def artifact(self):
        return self.boxed['one'].result.previous.capture.prepared.reconstructed.artifact

    def test_01_all_existing_systems_bound(self):
        for a in [*self.boxed.values(), self.linear]:
            self.assertTrue(a.report['binding_diagnostic_passed'])

    def test_02_legacy_outcomes_preserved(self):
        for word in ('one', 'two', 'three'):
            self.assertTrue(self.boxed[word].report['previous_completion_accepted'])
        self.assertEqual(self.boxed['budget'].report['previous_status'], 'infeasible')
        self.assertEqual(self.linear.report['previous_status'], 'inconsistent')

    def test_03_shapes_keep_every_ordered_entry(self):
        for word,shape in [('one',(43,12)),('two',(73,22)),('three',(111,36))]:
            h = self.boxed[word].report['system_binding']
            self.assertEqual((h['expected_rows'],h['expected_columns']),shape)

    def test_04_dimensions_zero(self):
        self.assertEqual(audit.coefficient_tags(0,0), (('constant',0,0),))
        for p,m in [(0,3),(3,0),(0,0)]:
            self.assertEqual(len(audit.coefficient_tags(p,m)),1+p+m*m)

    def test_05_invalid_dimension(self):
        for p,m in [(-1,0),(0,-1),(True,1),(1,False),(1.0,2)]:
            with self.assertRaises(ValueError): audit.coefficient_tags(p,m)

    def test_06_gram_row_major(self):
        tags=audit.coefficient_tags(2,3)
        self.assertEqual(tags[3],('gram',0,0))
        self.assertEqual(tags[4],('gram',0,1))
        self.assertEqual(tags[6],('gram',1,0))

    def test_07_non_symmetric_coefficients_not_collapsed(self):
        e=gram.LinearExprSpec(Q(2),(Q(3),),((Q(5),Q(7)),(Q(11),Q(13))))
        self.assertNotEqual(audit.coefficient(e,('gram',0,1)),audit.coefficient(e,('gram',1,0)))

    def test_08_fake_obstruction_rejected_by_binding(self):
        a=self.artifact();s=audit.family_system(a)
        fake=lin.System.make(s.columns,[[Q(0)]*s.columns for _ in s.rhs],
                             [Q(1)]+[Q(0)]*(len(s.rhs)-1))
        w=(Q(1),)+(Q(0),)*(len(s.rhs)-1)
        self.assertTrue(lin.is_obstruction(fake,w))
        self.assertFalse(audit.system_binding(a,fake)['matrix_and_rhs_match'])

    def test_09_missing_last_equation_rejected(self):
        a=self.artifact();s=audit.family_system(a)
        t=lin.System.make(s.columns,s.matrix[:-1],s.rhs[:-1])
        self.assertFalse(audit.system_binding(a,t)['dimensions_match'])

    def test_10_extra_column_rejected(self):
        a=self.artifact();s=audit.family_system(a)
        t=lin.System.make(s.columns+1,[r+(Q(0),) for r in s.matrix],s.rhs)
        self.assertFalse(audit.system_binding(a,t)['dimensions_match'])

    def test_11_rhs_mutation_precisely_located(self):
        a=self.artifact();s=audit.family_system(a);b=list(s.rhs);b[13]+=Q(1,10000)
        t=lin.System.make(s.columns,s.matrix,b);h=audit.system_binding(a,t)
        self.assertEqual(h['mismatches'],[dict(row=13,coefficient=('gram',1,0),column='rhs')])

    def test_12_multiplier_sign_error_rejected(self):
        a=self.artifact();s=audit.family_system(a);A=[list(r) for r in s.matrix]
        for i,row in enumerate(A):
            if row[1]: row[1] = -row[1]; break
        self.assertFalse(audit.system_binding(a,lin.System.make(s.columns,A,s.rhs))['matrix_and_rhs_match'])

    def test_13_duplicate_occurrences_remain_columns(self):
        a=self.artifact();u=a.upper
        v=replace(u,assumption_terms=u.assumption_terms+(u.assumption_terms[0],))
        s=audit.family_system(replace(a,upper=v))
        self.assertTrue(all(r[1]==r[-1] for r in s.matrix))
        self.assertEqual(s.columns,2+len(u.assumption_terms))

    def test_14_zero_reference_still_a_column(self):
        s=audit.family_system(self.artifact())
        self.assertEqual(s.columns,12)
        self.assertTrue(all(r[11]==0 for r in s.matrix))

    def test_15_no_assumptions_has_bound_column(self):
        a=self.artifact();s=audit.family_system(replace(a,upper=replace(a.upper,assumption_terms=())))
        self.assertEqual(s.columns,1);self.assertEqual(s.matrix[0][0],1)
        self.assertTrue(all(r[0]==0 for r in s.matrix[1:]))

    def test_16_bound_not_forced_nonnegative(self):
        self.assertTrue(audit.endpoint_binding((Q(-2),Q(-1,10000)),Q(1,1000),
            (Q(-2001,1000),Q(0)),(Q(-1999,1000),Q(9,10000))))

    def test_17_box_based_on_raw_not_seed(self):
        a=self.boxed['one'];r=a.result
        seed=(r.previous.capture.prepared.reconstructed.artifact.upper.bound,)+tuple(
            t.weight for t in r.previous.capture.prepared.reconstructed.artifact.upper.assumption_terms)
        self.assertTrue(audit.endpoint_binding(a.raw_vector,r.previous.capture.prepared.policy.max_abs_error,
                                               r.box.lower,r.box.upper))
        shifted=tuple(q+Q(1,10000) for q in seed)
        self.assertFalse(audit.endpoint_binding(shifted,r.previous.capture.prepared.policy.max_abs_error,
                                                r.box.lower,r.box.upper))

    def test_18_wrong_endpoint_rejected(self):
        a=self.boxed['budget'];b=a.result.box;l=list(b.lower);l[0]+=Q(1,10000)
        self.assertFalse(audit.endpoint_binding(a.raw_vector,Q(1,1000),tuple(l),b.upper))

    def test_19_length_sensitive_endpoints(self):
        self.assertFalse(audit.endpoint_binding((Q(0),),Q(1),(),()))
        self.assertFalse(audit.endpoint_binding((Q(0),),Q(1),(Q(-1),Q(0)),(Q(1),Q(0))))

    def test_20_raw_vector_and_references_both_bound(self):
        a=self.boxed['one'];p=a.result.previous.capture.prepared
        self.assertTrue(audit.vector_binding(p.reconstructed.artifact.upper,p.raw.artifact.upper,a.raw_vector))
        self.assertFalse(audit.vector_binding(p.reconstructed.artifact.upper,p.raw.artifact.upper,a.raw_vector[:-1]))
        t=p.raw.artifact.upper.assumption_terms
        changed=replace(p.raw.artifact.upper,assumption_terms=(replace(t[0],index=(t[0].index+1)%11),)+t[1:])
        self.assertFalse(audit.vector_binding(p.reconstructed.artifact.upper,changed,a.raw_vector))

    def test_21_generic_random_coefficient_identity(self):
        rng=random.Random(1232)
        for p,m,q in [(0,0,0),(0,2,3),(2,0,2),(3,3,4)]:
            def expr():return gram.LinearExprSpec(Q(rng.randrange(-4,5)),tuple(Q(rng.randrange(-4,5)) for _ in range(p)),
                tuple(tuple(Q(rng.randrange(-4,5)) for _ in range(m)) for _ in range(m)))
            rows=[expr() for _ in range(max(q,1))];o=expr();S=expr().gram_coeff
            u=gram.UpperSpec(Q(0),o,(),tuple(gram.AssumptionTermSpec(Q(0),i) for i in range(q)),S,gram.FactorCertSpec(()))
            artifact=SimpleNamespace(upper=u)
            with patch.object(audit.sparse,'compact_snapshot',return_value=SimpleNamespace(constraints=rows)):
                s=audit.family_system(artifact)
            x=tuple(Q(rng.randrange(-5,6),3) for _ in range(q+1))
            for i,tag in enumerate(audit.coefficient_tags(p,m)):
                lhs=x[0]*(tag[0]=='constant')-audit.coefficient(o,tag)
                rhs=sum(x[j+1]*audit.coefficient(rows[j],tag) for j in range(q))
                if tag[0]=='gram':rhs+=S[tag[1]][tag[2]]
                self.assertEqual(lhs-rhs,sum(s.matrix[i][j]*x[j] for j in range(q+1))-s.rhs[i])

    def test_22_linear_obstruction_reused(self):
        r=self.linear.result
        self.assertTrue(lin.is_obstruction(r.system,r.linear.obstruction))

    def test_23_budget_obstruction_reused(self):
        r=self.boxed['budget'].result
        self.assertTrue(box.verify_result(r.box,r.result))
        self.assertEqual(box.obstruction_value(r.box,r.result.obstruction),Q(-21,10000))

    def test_24_no_new_fixture_or_live_claim(self):
        for a in [*self.boxed.values(),self.linear]:
            self.assertFalse(a.report['lean_checked']);self.assertFalse(a.report['live_capture_performed'])
            self.assertFalse(a.report['python_compiler_verified'])

    def test_25_negative_replays_bind_before_conclusion(self):
        for a,claim in [(self.linear,'no_fixed_family_certificate'),(self.boxed['budget'],'no_fixed_family_in_budget')]:
            text=audit.render_binding_replay(a,'LeanPEP.Imported.D12Test')
            self.assertIn('compiler_binding',text);self.assertIn(claim,text)
            self.assertIn('audited_trace_check',text);self.assertIn('audited_raw_vector',text)
            self.assertNotIn('theorem actual_upper',text)

    def test_26_positive_replay_keeps_old_acceptance(self):
        text=audit.render_binding_replay(self.boxed['one'],'LeanPEP.Imported.D12Test')
        self.assertIn('theorem actual_upper',text);self.assertIn('compiler_box_binding',text)
        self.assertIn('compiled_family_accepted',text);self.assertNotIn('native_decide',text)

    def test_27_original_outputs_preserved(self):
        a=self.boxed['one'];ns='LeanPEP.Imported.D12Test';d=Path('/tmp/d12-output')
        old=audit.bounded.outputs(a.result,d,ns);new=audit.outputs(a,d,ns)
        self.assertTrue(all(new[k]==v for k,v in old.items()))
        self.assertEqual(set(new)-set(old),{d/'BindingReplay.lean',d/'compiler_binding_report.json'})

    def test_28_corrupted_system_not_laundered(self):
        original=audit.linear.coefficient_system
        def broken(a):
            s=original(a);b=list(s.rhs);b[0]+=1
            return lin.System.make(s.columns,s.matrix,b)
        with patch.object(audit.linear,'coefficient_system',side_effect=broken):
            a=audit.run(copy.deepcopy(self.inputs['one']),'linear')
        self.assertFalse(a.report['binding_diagnostic_passed'])
        text=audit.render_binding_replay(a,'LeanPEP.Imported.D12Bad')
        self.assertNotIn('theorem no_fixed_family_certificate',text)

    def test_29_cli_success(self):
        with tempfile.TemporaryDirectory() as d:
            r=subprocess.run([sys.executable,str(ROOT/'tools/audit_compiled_completion.py'),
                str(ROOT/'data/fixtures/pepit_bounded/pg_one.json'),'--output-dir',d,
                '--namespace','LeanPEP.Imported.D12CLI'],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertTrue((Path(d)/'BindingReplay.lean').is_file())

    def test_30_cli_refuses_stale_files(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'completed_exact.json';p.write_text('old')
            r=subprocess.run([sys.executable,str(ROOT/'tools/audit_compiled_completion.py'),
                str(ROOT/'data/fixtures/pepit_bounded/pg_one.json'),'--output-dir',d,
                '--namespace','LeanPEP.Imported.D12CLI'],capture_output=True,text=True)
            self.assertEqual(r.returncode,1);self.assertEqual(p.read_text(),'old')

    def test_31_invalid_mode(self):
        with self.assertRaises(ValueError):audit.run(self.inputs['one'],'automatic')

    def test_32_limit_not_infeasibility(self):
        a=audit.run(self.inputs['one'],'box',max_pivots=0)
        self.assertEqual(a.report['previous_status'],'limit')
        self.assertNotIn('no_fixed_family_in_budget',audit.render_binding_replay(a,'LeanPEP.Imported.D12Limit'))


if __name__=='__main__': unittest.main()
