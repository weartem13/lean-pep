from __future__ import annotations

import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as src
import import_proximal_gradient_coordinates as co
import regenerate_proximal_gradient_coordinates as gen
import regenerate_proximal_gradient_source as oldgen
import synthesize_psd_factors as psd

ROOT=Path(__file__).resolve().parents[2]


def raw(T=1):
    names={1:'one',2:'two',3:'three'}
    if T in names:
        return gram.load_json(ROOT/f'data/fixtures/composite_coordinates/pg_{names[T]}_step.json')
    return gen.fixture(T)


def report(x): return co.diagnose(co.parse_artifact(x))
def q(x): return src.exact_json(Q(x))
def transpose(A): return tuple(tuple(A[i][j] for i in range(len(A))) for j in range(len(A[0])))
def mm(A,B): return tuple(tuple(sum((a*b for a,b in zip(row,col)),Q(0)) for col in transpose(B)) for row in A)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def gram_matrix(V): return tuple(tuple(dot(a,b) for b in V) for a in V)
def evaluate(e,F,G):
    return e.const+dot(e.value_coeff,F)+sum((e.gram_coeff[i][j]*G[i][j] for i in range(len(G)) for j in range(len(G))),Q(0))


class CoordinatesTests(unittest.TestCase):
    def test_committed_fixtures_all_guards(self):
        for T in (1,2,3):
            r=report(raw(T))
            self.assertTrue(r['diagnostic_passed'])
            self.assertTrue(all(r['source_guards'].values()))
            self.assertFalse(r['lean_checked'])
            self.assertFalse(r['live_capture_performed'])

    def test_dimensions_and_no_extra_value(self):
        for T in range(1,9):
            p,m,k=co.dimensions(T)
            self.assertEqual((p,m,k),(2*T+3,2*T+3,2*T+4))
            s=gen.native_snapshot(T)
            self.assertEqual(len(s.smooth_samples),T+2)
            self.assertEqual(len(s.nonsmooth_samples),T+1)
            self.assertEqual(len(s.constraints),(T+2)**2+(T+1)**2+1)

    def test_rectangular_retraction_not_inverse(self):
        for m in range(1,18):
            C,J=co.maps(m)
            self.assertEqual(mm(C,J),tuple(src.unit(m,i) for i in range(m)))
            self.assertNotEqual(mm(J,C),tuple(src.unit(m+1,i) for i in range(m+1)))
            self.assertEqual(mm(J,C)[0][0],0)

    def test_native_samples_and_full_coefficients_independent(self):
        for T in range(1,9):
            s=gen.native_snapshot(T);e=src.expected_snapshot(T)
            self.assertEqual(s.smooth_samples,tuple(map(co.lift_sample,e.smooth_samples)))
            self.assertEqual(s.nonsmooth_samples,tuple(map(co.lift_sample,e.nonsmooth_samples)))
            self.assertEqual(s.constraints,tuple(map(co.lift_expr,e.constraints)))
            self.assertEqual(s.objective,co.lift_expr(e.objective))

    def test_native_constraint_values_arbitrary_translated_frames(self):
        for T in range(1,7):
            s=gen.native_snapshot(T);e=src.expected_snapshot(T);p,m,k=co.dimensions(T);C,_=co.maps(m)
            F=tuple(Q(i*i-2*i-1,3) for i in range(p))
            for dim in (0,1,3,5):
                V=tuple(tuple(Q((i+2)*(j+3)%11-5,3) for j in range(dim)) for i in range(k))
                Z=tuple(tuple(sum((C[i][a]*V[a][j] for a in range(k)),Q(0)) for j in range(dim)) for i in range(m))
                G,H=gram_matrix(V),gram_matrix(Z)
                for a,b in zip(s.constraints+(s.objective,),e.constraints+(e.objective,),strict=True):
                    self.assertEqual(evaluate(a,F,G),evaluate(b,F,H))

    def test_scalar_zero_origin_evaluation_no_symmetry_assumption(self):
        for m in range(1,8):
            S=tuple(tuple(Q(2*i-3*j,5) for j in range(m+1)) for i in range(m+1))
            e=gram.LinearExprSpec(Q(7,3),(Q(1),Q(-2)),S)
            G=tuple(tuple(Q(4*i+j-2,7) for j in range(m)) for i in range(m))
            G0=((Q(0),)*(m+1),)+tuple((Q(0),)+row for row in G)
            self.assertEqual(evaluate(e,(Q(2),Q(3)),G0),evaluate(co.restrict_expr(e),(Q(2),Q(3)),G))

    def test_coefficient_congruence_no_symmetrization(self):
        for m in range(1,8):
            S=tuple(tuple(Q(5*i-j+1,3) for j in range(m)) for i in range(m))
            C,J=co.maps(m)
            self.assertEqual(co.lift_matrix(S),mm(mm(transpose(C),S),C))
            self.assertEqual(co.restrict_matrix(co.lift_matrix(S)),S)

    def test_points_and_oracles_have_distinct_origin_terms(self):
        s=co.lift_sample(src.Sample(1,(Q(2),Q(3)),(Q(4),Q(5))))
        self.assertEqual(s.position,(Q(-1),Q(2),Q(3)))
        self.assertEqual(s.oracle,(Q(-4),Q(4),Q(5)))
        self.assertEqual(co.restrict_sample(s),src.Sample(1,(Q(2),Q(3)),(Q(4),Q(5))))

    def test_star_gradient_cancellation_not_separate_stationarity(self):
        s=gen.native_snapshot(2)
        self.assertEqual(s.smooth_samples[0].position[0],1)
        self.assertEqual(s.smooth_samples[0].oracle[2],1)
        self.assertEqual(s.nonsmooth_samples[0].oracle[2],-1)

    def test_certificate_targets_and_weights_against_previous(self):
        for T in range(1,7):
            a=co.parse_artifact(raw(T));b=src.parse_artifact(oldgen.fixture(T));c=co.restrict_upper(a.upper)
            self.assertEqual(a.upper.dual_matrix,co.lift_matrix(b.upper.dual_matrix))
            self.assertEqual(c.dual_matrix,b.upper.dual_matrix)
            self.assertEqual(c.assumption_terms,b.upper.assumption_terms)
            self.assertEqual(c.bound,b.upper.bound)
            self.assertEqual(c.objective,b.upper.objective)
            self.assertTrue(co.local_check(co.restrict_snapshot(a),c)['accepted'])

    def test_factor_restriction_exact(self):
        for T in (1,2,3):
            a=co.parse_artifact(raw(T));c=co.restrict_upper(a.upper);m=co.dimensions(T)[1]
            fs=tuple(psd.Factor(t.weight,t.vector) for t in c.dual_factor.factors)
            self.assertEqual(psd.reconstruct(m,fs),c.dual_matrix)
            self.assertEqual([x.weight for x in a.upper.dual_factor.factors],[x.weight for x in fs])

    def test_hidden_origin_constraint_passes_restriction_but_rejected(self):
        x=raw();x['source']['constraints'][0]['gram_coeff'][0][0]=q(1)
        r=report(x)
        self.assertTrue(r['source_guards']['centered_source'])
        self.assertTrue(r['bound_guards']['centered_bound'])
        self.assertTrue(r['native_certificate']['accepted']) # zero multiplier on this self-pair
        self.assertFalse(r['source_guards']['constraints_roundtrip'])
        self.assertFalse(r['diagnostic_passed'])

    def test_hidden_origin_objective_rejected(self):
        x=raw();x['source']['objective']['gram_coeff'][0][0]=q(1)
        r=report(x)
        self.assertTrue(r['source_guards']['centered_source'])
        self.assertFalse(r['source_guards']['objective_roundtrip'])

    def test_hidden_origin_cross_term_rejected(self):
        for i,j in ((0,1),(1,0),(0,3),(3,0)):
            x=raw();x['source']['constraints'][0]['gram_coeff'][i][j]=q(Q(1,10**80))
            r=report(x)
            self.assertTrue(r['source_guards']['centered_source'])
            self.assertFalse(r['source_guards']['constraints_roundtrip'])

    def test_point_origin_pollution_not_erased_by_audit(self):
        x=raw()
        for s in x['source']['smooth_samples']:
            s['position'][0]=q(Q(s['position'][0]['num'],s['position'][0]['den'])+1)
        r=report(x)
        self.assertTrue(r['source_guards']['centered_source'])
        self.assertFalse(r['source_guards']['smooth_roundtrip'])

    def test_oracle_origin_pollution_rejected(self):
        x=raw();x['source']['nonsmooth_samples'][0]['oracle'][0]=q(1)
        r=report(x)
        self.assertTrue(r['source_guards']['centered_source'])
        self.assertFalse(r['source_guards']['nonsmooth_roundtrip'])

    def test_wrong_center_map_sign_rejected(self):
        x=raw();x['source']['center_matrix'][0][0]=q(1)
        r=report(x)
        self.assertTrue(r['bound_guards']['centered_bound'])
        self.assertFalse(r['source_guards']['center_matrix'])

    def test_wrong_zero_origin_section_rejected(self):
        x=raw();x['source']['section_matrix'][0][0]=q(1)
        self.assertFalse(report(x)['source_guards']['section_matrix'])

    def test_mutually_inverse_wrong_maps_still_rejected(self):
        x=raw();x['source']['center_matrix'][2][3]=q(-1);x['source']['section_matrix'][3][2]=q(-1)
        a=co.parse_artifact(x);m=co.dimensions(1)[1]
        self.assertEqual(mm(a.center_matrix,a.section_matrix),tuple(src.unit(m,i) for i in range(m)))
        self.assertFalse(co.diagnose(a)['diagnostic_passed'])

    def test_hidden_native_dual_error_passes_centered_only(self):
        x=raw();x['upper']['dual_matrix'][0][0]=q(99)
        r=report(x)
        self.assertTrue(r['bound_guards']['source'])
        self.assertTrue(r['bound_guards']['centered_bound'])
        self.assertFalse(r['bound_guards']['native_certificate'])

    def test_hidden_native_factor_error_rejected(self):
        x=raw();x['upper']['dual_factor']['factors'][0]['vector'][0]=q(99)
        r=report(x)
        self.assertTrue(r['bound_guards']['centered_bound'])
        self.assertFalse(r['native_certificate']['factor'])

    def test_negative_weight_rejected(self):
        x=raw();x['upper']['assumption_terms'][0]['weight']=q(-1)
        self.assertFalse(report(x)['native_certificate']['weights'])

    def test_wrong_bound_rejected(self):
        x=raw();x['upper']['bound']=q(0)
        self.assertFalse(report(x)['native_certificate']['identity'])

    def test_empty_implicit_guard_not_dropped(self):
        x=raw();x['upper']['interp_terms']=[dict(weight=q(0),i=0,j=1)]
        r=report(x)
        self.assertTrue(r['native_certificate']['accepted'])
        self.assertFalse(r['bound_guards']['empty_implicit_interpolation'])
        self.assertFalse(r['bound_guards']['centered_bound'])

    def test_missing_extra_and_reordered_constraints(self):
        a=co.parse_artifact(raw());s=a.source
        for cs in (s.constraints[:-1],s.constraints+(s.constraints[0],),tuple(reversed(s.constraints))):
            x=replace(a,source=replace(s,constraints=cs))
            # Avoid an invalid typed index in the truncated local checker.
            x=replace(x,upper=replace(x.upper,assumption_terms=()))
            self.assertFalse(co.diagnose(x)['source_guards']['centered_source'])

    def test_header_values_scales_and_sense(self):
        for key,value in [('steps',4),('smoothness',q(2)),('step_size',q(2)),('radius_squared',q(2)),
                          ('sense','leZero'),('coordinates','made-up'),('basis_count',5),('value_count',8)]:
            x=raw();x['source']['header'][key]=value
            self.assertFalse(report(x)['source_guards']['header'])

    def test_order_tags_and_value_slots_not_repaired(self):
        for key in ('basis_order','value_order','constraint_order'):
            x=raw();seq=x['source']['header'][key];seq[0],seq[1]=seq[1],seq[0]
            self.assertFalse(report(x)['source_guards']['header'])
        x=raw();x['source']['smooth_samples'][0]['value_index']=1
        self.assertFalse(report(x)['source_guards']['centered_source'])

    def test_primal_gram_is_not_a_principal_block(self):
        # Native vectors [x_star,x0]=[2,3]; centered displacement is 1, not 3.
        C,J=co.maps(1)
        G=((Q(4),Q(6)),(Q(6),Q(9)))
        self.assertEqual(mm(mm(C,G),transpose(C)),((Q(1),),))
        self.assertEqual(co.restrict_matrix(G),((Q(9),),))
        self.assertNotEqual(co.restrict_matrix(G),mm(mm(C,G),transpose(C)))

    def test_scalar_values_not_centered_to_zero(self):
        a=co.parse_artifact(raw());c=co.restrict_snapshot(a)
        self.assertEqual(c.objective.value_coeff,(Q(-1),Q(0),Q(1),Q(-1),Q(1)))
        self.assertEqual(c.smooth_samples[0].value_index,0)
        self.assertEqual(c.nonsmooth_samples[0].value_index,3)

    def test_parser_horizon_and_caller_choice(self):
        for T in (0,-1,True,'1',1.0):
            x=raw();x['horizon']=T
            with self.assertRaises(ValueError): co.parse_artifact(x)
        with self.assertRaises(ValueError): co.parse_artifact(raw(),2)

    def test_parser_unknown_and_duplicate_fields(self):
        for path in ((),('source',),('source','header'),('upper',)):
            x=raw();s=x
            for k in path:s=s[k]
            s['extra']=3
            with self.assertRaises(ValueError):co.parse_artifact(x)
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'duplicate.json';p.write_text('{"horizon":1,"horizon":2}')
            with self.assertRaises(ValueError):gram.load_json(p)

    def test_parser_rectangular_shapes_and_indices(self):
        for key in ('center_matrix','section_matrix'):
            x=raw();x['source'][key].pop()
            with self.assertRaises(ValueError):co.parse_artifact(x)
        x=raw();x['source']['smooth_samples'][0]['position'].pop()
        with self.assertRaises(ValueError):co.parse_artifact(x)
        x=raw();x['upper']['assumption_terms'][0]['index']=999
        with self.assertRaises(ValueError):co.parse_artifact(x)

    def test_parser_no_float_decimal_or_boolean_rationals(self):
        for v in (0.5,'1/2',True,dict(num=1,den=0),dict(num=True,den=2)):
            x=raw();x['source']['center_matrix'][0][0]=v
            with self.assertRaises(ValueError):co.parse_artifact(x)

    def test_nonreduced_exact_rationals_preserved_semantically(self):
        x=raw();x['source']['center_matrix'][0][0]=dict(num=-2,den=2)
        self.assertTrue(report(x)['diagnostic_passed'])

    def test_renderer_literal_native_data_no_acceptance(self):
        x=raw();x['origin']['description']=src.AS+' exactly this producer text'
        x['source']['center_matrix'][0][0]=q(17)
        a=co.parse_artifact(x);text=co.render_module(a,'LeanPEP.Imported.Test.Native')
        self.assertIn('def sourceQ : SourceQ 0',text)
        self.assertIn('centerMatrix := ![![(17 : ℚ)',text)
        self.assertIn(src.AS+' exactly this producer text',text)
        self.assertNotIn('theorem ',text)
        self.assertNotIn('native_decide',text)
        self.assertNotIn('expectedSourceQ',text)

    def test_generated_centered_json_uses_unchanged_D2_importer(self):
        for T in (1,2,3):
            a=co.parse_artifact(raw(T));b=src.parse_artifact(co.centered_json(a),T)
            self.assertTrue(src.diagnose(b)['diagnostic_passed'])
            self.assertEqual(a.upper.bound,b.upper.bound)
            self.assertEqual(a.upper.assumption_terms,b.upper.assumption_terms)

    def test_regeneration_deterministic(self):
        for path,text in gen.generate().items():
            self.assertEqual(path.read_text(),text)

    def test_cli_outputs_and_guarded_exit(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);inp=p/'input.json';inp.write_text(json.dumps(raw()))
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_coordinates.py'),str(inp),
                '--lean',str(p/'source.lean'),'--report',str(p/'report.json'),'--namespace','LeanPEP.Imported.Test.Native',
                '--centered-json',str(p/'centered.json'),'--expected-steps','1','--require-diagnostic-pass']
            a=subprocess.run(cmd,capture_output=True,text=True)
            self.assertEqual(a.returncode,0,a.stderr)
            self.assertTrue(src.diagnose(src.parse_artifact(gram.load_json(p/'centered.json')))['diagnostic_passed'])
            x=raw();x['source']['section_matrix'][0][0]=q(1);inp.write_text(json.dumps(x))
            a=subprocess.run(cmd,capture_output=True,text=True)
            self.assertEqual(a.returncode,2)
            self.assertFalse(json.loads((p/'report.json').read_text())['diagnostic_passed'])
            self.assertTrue((p/'source.lean').is_file())

    def test_cli_path_collision_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);inp=p/'input.json';inp.write_text(json.dumps(raw()))
            before=inp.read_bytes()
            r=subprocess.run([sys.executable,str(ROOT/'tools/import_proximal_gradient_coordinates.py'),str(inp),
                '--lean',str(inp),'--report',str(p/'r.json'),'--namespace','LeanPEP.Imported.Test.X'],capture_output=True)
            self.assertEqual(r.returncode,2)
            self.assertEqual(inp.read_bytes(),before)

    def test_source_has_no_trusted_generator_or_solver_requirement(self):
        text=(ROOT/'LeanPEP/Adapters/ProximalGradientCoordinates.lean').read_text()
        self.assertIn('checkSourceQ_sound',text)
        self.assertIn('checkUpperCertQ c',text)
        self.assertIn('ProximalGradientSource.checkBoundQ (centeredSourceQ s)',text)
        for token in ('sorry','admit','native_decide','unsafe','Float'):
            self.assertNotIn(token,text)


if __name__=='__main__':unittest.main()
