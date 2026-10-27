"""D1 synthesis: exact, independent checks; no Lean acceptance is inferred here."""
from __future__ import annotations
import copy
from dataclasses import replace
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

import import_exact_gram_bundle as gram
import synthesize_psd_factors as s
import regenerate_psd_synthesis as regen
from tests.python import test_proximal_gradient_certificate as pg

ROOT = Path(__file__).resolve().parents[2]


def determinant(a):
    if not a:
        return Q(1)
    return sum(((-1)**j*a[0][j]*determinant(tuple(
        tuple(row[k] for k in range(len(a)) if k != j) for row in a[1:]))
        for j in range(len(a))), Q(0))


def all_principal_minors_nonnegative(a):
    for k in range(1,len(a)+1):
        for inds in itertools.combinations(range(len(a)),k):
            if determinant(tuple(tuple(a[i][j] for j in inds) for i in inds)) < 0:
                return False
    return True


def strip_factors(raw):
    raw = copy.deepcopy(raw)
    raw['primal'].pop('gram_factor')
    raw['upper'].pop('dual_factor')
    raw['declared'].pop('primal_factor_count')
    raw['declared'].pop('dual_factor_count')
    return raw


class ExactPSDSynthesisTests(unittest.TestCase):
    def good(self, a, order=None):
        a = s.exact_matrix(a)
        r = s.synthesize_psd(a,pivot_order=order)
        self.assertTrue(s.verify_result(a,r))
        self.assertEqual(r.status,'psd')
        self.assertEqual(s.reconstruct(len(a),r.factors),a)
        self.assertTrue(all(t.weight>0 for t in r.factors))
        self.assertLessEqual(len(r.factors),len(a))
        return r

    def bad(self,a,order=None):
        a=s.exact_matrix(a);r=s.synthesize_psd(a,pivot_order=order)
        self.assertEqual(r.status,'negative');self.assertTrue(s.verify_result(a,r))
        self.assertLess(s.quadratic(a,r.witness),0)
        return r

    def raw_bundle(self,name='one_step_exact.json'):
        return gram.load_json(ROOT/'data/fixtures/gram_external'/name)

    def test_empty_dimension(self):
        self.assertEqual(self.good([]).factors,())

    def test_zero_matrices(self):
        for n in range(1,9):self.assertEqual(self.good([[0]*n for _ in range(n)]).factors,())

    def test_irrational_cholesky_not_needed(self):
        r=self.good([[2,1],[1,3]])
        self.assertEqual(tuple(t.weight for t in r.factors),(Q(2),Q(5,2)))

    def test_leading_zero_row_and_permutation(self):
        r=self.good([[0,0,0],[0,2,2],[0,2,2]],[2,0,1])
        self.assertEqual(r.pivots,(2,));self.assertEqual(r.factors[0].vector,(0,1,1))

    def test_singular_dense(self):
        self.assertEqual(len(self.good([[1,2,3],[2,4,6],[3,6,9]]).factors),1)

    def test_small_exact_positive_pivot_not_dropped(self):
        r=self.good([[Q(1,10**40),0],[0,1]])
        self.assertEqual(len(r.factors),2)

    def test_small_negative_is_rejected(self):
        self.bad([[1,0],[0,-Q(1,10**40)]])

    def test_zero_diagonal_nonzero_row(self):
        r=self.bad([[0,1],[1,3]])
        self.assertEqual(r.quadratic_value,-1)

    def test_negative_diagonal(self):
        self.bad([[-1,0],[0,3]])

    def test_positive_diagonal_indefinite(self):
        r=self.bad([[1,2],[2,1]])
        self.assertEqual(r.witness,(Q(-2),Q(1)));self.assertEqual(r.quadratic_value,-3)

    def test_negative_witness_is_lifted_to_original_basis(self):
        a=[[1,1,1],[1,1,2],[1,2,3]]
        r=self.bad(a)
        self.assertNotEqual(r.witness[0],0)
        for f in r.factors:
            self.assertEqual(sum(x*y for x,y in zip(f.vector,r.witness)),0)

    def test_negative_lift_under_permutations(self):
        a=[[2,1,2],[1,2,4],[2,4,1]]
        for perm in itertools.permutations(range(3)):self.bad(a,perm)

    def test_asymmetry_not_silently_averaged(self):
        a=s.exact_matrix([[1,1],[0,1]]);r=s.synthesize_psd(a)
        self.assertEqual(r.status,'asymmetric');self.assertTrue(s.verify_result(a,r))
        self.assertIsNone(r.witness)

    def test_exhaustive_symmetric_three_by_three(self):
        # Independent criterion, not another elimination implementation.
        for entries in itertools.product((-1,0,1),repeat=6):
            x,y,z,a,b,c=map(Q,entries)
            m=((x,a,b),(a,y,c),(b,c,z))
            expected=all_principal_minors_nonnegative(m)
            r=s.synthesize_psd(m)
            self.assertEqual(r.status=='psd',expected,msg=str(m))
            self.assertTrue(s.verify_result(m,r))

    def test_random_rectangular_gram_constructions(self):
        rng=random.Random(731)
        for n in (0,1,2,5,9):
            for k in (0,1,2,6):
                fs=[s.Factor(Q(rng.randint(1,5),rng.randint(1,5)),
                    tuple(Q(rng.randint(-4,4),rng.randint(1,7)) for _ in range(n))) for _ in range(k)]
                a=s.reconstruct(n,fs)
                order=list(range(n));rng.shuffle(order)
                self.good(a,order)

    def test_congruence_indefinite(self):
        # Rational invertible triangular congruences preserve a negative direction.
        rng=random.Random(7)
        for n in (2,3,5,8):
            b=[[Q(1) if i==j else Q(rng.randint(-3,3)) if i>j else Q(0)
                for j in range(n)] for i in range(n)]
            d=[Q(1)]*(n-1)+[Q(-1,7)]
            a=tuple(tuple(sum(b[i][k]*d[k]*b[j][k] for k in range(n))
                          for j in range(n)) for i in range(n))
            self.bad(a)

    def test_both_existing_gd_roles(self):
        b=gram.parse_bundle(self.raw_bundle())
        self.good(b.primal.gram);r=self.good(b.upper.dual_matrix)
        self.assertEqual(len(r.factors),2)

    def test_proximal_matrices_1_to_16(self):
        for T in range(1,17):
            factors=[s.Factor(w,v) for w,v in pg.factors(T)]
            a=s.reconstruct(2*T+3,factors)
            r=self.good(a)
            self.assertEqual(len(r.factors),2*T+1)
            self.good(pg.data(T)[-1])

    def test_bundle_only_factors_and_counts_change(self):
        raw=self.raw_bundle();before=copy.deepcopy(raw)
        out,report=s.refactor_bundle(raw)
        self.assertEqual(raw,before)
        self.assertEqual(strip_factors(out),strip_factors(raw))
        self.assertEqual(out['declared']['dual_factor_count'],2)
        self.assertEqual(report['full_bundle_acceptance'],'not_checked')
        self.assertEqual(report['source_formulation_audit'],'not_performed')

    def test_existing_factors_not_used_in_synthesis(self):
        raw=self.raw_bundle()
        raw['primal']['gram_factor']={'factors':[]};raw['upper']['dual_factor']={'factors':[]}
        raw['declared']['primal_factor_count']=0;raw['declared']['dual_factor_count']=0
        out,_=s.refactor_bundle(raw)
        self.assertEqual(out['declared']['primal_factor_count'],1)
        self.assertEqual(out['declared']['dual_factor_count'],2)

    def test_bad_factor_is_repaired_not_bad_matrix(self):
        raw=self.raw_bundle('one_step_bad_primal_factor.json')
        out,_=s.refactor_bundle(raw);self.assertIsNotNone(out)
        self.assertEqual(strip_factors(out),strip_factors(raw))
        raw['primal']['gram'][0][0]={'num':-1,'den':1}
        out,r=s.refactor_bundle(raw);self.assertIsNone(out);self.assertEqual(r['primal']['status'],'negative')

    def test_invalid_full_bound_is_not_repaired(self):
        raw=self.raw_bundle();raw['upper']['bound']={'num':0,'den':1}
        out,r=s.refactor_bundle(raw)
        self.assertIsNotNone(out);self.assertEqual(out['upper']['bound'],raw['upper']['bound'])
        self.assertEqual(r['full_bundle_acceptance'],'not_checked')

    def test_unrelated_bad_metadata_is_not_repaired(self):
        raw=self.raw_bundle();raw['declared']['ordered_pair_count']=1
        out,_=s.refactor_bundle(raw)
        self.assertEqual(out['declared']['ordered_pair_count'],1)

    def test_failed_dual_emits_no_partial_bundle(self):
        raw=self.raw_bundle();raw['upper']['dual_matrix'][0][0]={'num':-1,'den':1}
        out,r=s.refactor_bundle(raw)
        self.assertIsNone(out);self.assertFalse(r['bundle_emitted'])
        self.assertEqual(r['primal']['status'],'psd')

    def test_factor_mutation_detected(self):
        a=s.exact_matrix([[2,1],[1,3]]);r=s.synthesize_psd(a)
        self.assertFalse(s.verify_result(a,replace(r,factors=r.factors[:1])))
        bad=s.Factor(-r.factors[0].weight,r.factors[0].vector)
        self.assertFalse(s.verify_result(a,replace(r,factors=(bad,)+r.factors[1:])))

    def test_matrix_mutation_detected(self):
        a=s.exact_matrix([[2,1],[1,3]]);r=s.synthesize_psd(a)
        self.assertFalse(s.verify_result([[2,1],[1,4]],r))

    def test_negative_witness_mutation_detected(self):
        a=s.exact_matrix([[1,2],[2,1]]);r=s.synthesize_psd(a)
        self.assertFalse(s.verify_result(a,replace(r,witness=(Q(0),Q(1)))))
        self.assertFalse(s.verify_result(a,replace(r,quadratic_value=Q(-1))))

    def test_wrong_dimension_detected(self):
        a=s.exact_matrix([[2,1],[1,3]]);r=s.synthesize_psd(a)
        self.assertFalse(s.verify_result(a,replace(r,dimension=3)))

    def test_ragged_matrix_rejected(self):
        for a in ([[1,2]],[[1],[2,3]],'x'):
            with self.assertRaises(ValueError):s.synthesize_psd(a)

    def test_nonexact_api_input_rejected(self):
        for v in (1.0,True,'1',complex(1)):
            with self.assertRaises(ValueError):s.synthesize_psd([[v]])

    def test_bad_permutation_rejected(self):
        for p in ([0,0],[0],[False,1],[1,2]):
            with self.assertRaises(ValueError):s.synthesize_psd([[1,0],[0,1]],pivot_order=p)

    def test_json_exact_boundary(self):
        raw={'format':s.INPUT_FORMAT,'dimension':1,'matrix':[[{'num':1,'den':2}]]}
        self.assertEqual(s.parse_matrix_input(raw),((Q(1,2),),))
        for bad in (1.0,True,'0.5',{'num':1,'den':0},{'num':1.0,'den':2}):
            altered=copy.deepcopy(raw);altered['matrix'][0][0]=bad
            with self.assertRaises(ValueError):s.parse_matrix_input(altered)

    def test_unknown_json_key_rejected(self):
        raw={'format':s.INPUT_FORMAT,'dimension':0,'matrix':[],'tolerance':1}
        with self.assertRaises(ValueError):s.parse_matrix_input(raw)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaises(ValueError):
            json.loads('{"matrix":[],"matrix":[]}',object_pairs_hook=gram.reject_duplicate_pairs)

    def test_render_has_original_target_and_kernel_decision(self):
        a=s.exact_matrix([[2,1],[1,3]]);r=s.synthesize_psd(a)
        lean=s.render_matrix_lean(a,r,'LeanPEP.Imported.Example')
        self.assertIn('decide +kernel',lean);self.assertNotIn('native_decide',lean)
        self.assertIn('def matrixQ : Gram 2 ℚ := ![',lean)
        self.assertNotIn(':= factorGramQ',lean)

    def test_render_rejects_corrupt_result(self):
        a=s.exact_matrix([[2,1],[1,3]]);r=s.synthesize_psd(a)
        with self.assertRaises(ValueError):s.render_matrix_lean(a,replace(r,factors=()),'LeanPEP.Imported.Example')

    def test_render_negative_and_asymmetry(self):
        for a in ([[1,2],[2,1]],[[1,1],[0,1]]):
            a=s.exact_matrix(a);r=s.synthesize_psd(a)
            lean=s.render_matrix_lean(a,r,'LeanPEP.Imported.Example')
            self.assertIn('not_psd_rational',lean);self.assertNotIn('native_decide',lean)

    def test_bundle_renderer_uses_existing_importer_without_acceptance(self):
        out,_=s.refactor_bundle(self.raw_bundle());lean=s.render_bundle_data(out,'LeanPEP.Imported.Example')
        self.assertIn('tools/import_exact_gram_bundle.py',lean)
        self.assertNotIn('native_decide',lean);self.assertNotIn('theorem bundleQ_check',lean)
        self.assertEqual(out['expect'],'accepted') # Not rewritten in JSON.

    def test_namespace_injection_rejected(self):
        with self.assertRaises(ValueError):
            s.render_matrix_lean((),s.synthesize_psd([]),'X\naxiom bad : False')

    def test_generated_files_reproducible(self):
        for path,text in regen.generate().items():
            self.assertEqual(path.read_text(),text,msg=str(path))

    def test_matrix_input_report_does_not_claim_lean_or_solver(self):
        a=s.exact_matrix([[1]]);r=s.result_report(a,s.synthesize_psd(a))
        self.assertEqual(r['lean_status'],'not_run_by_this_producer')
        self.assertIn('matrix only',r['scope'])

    def test_original_checker_sources_are_used(self):
        src=(ROOT/'LeanPEP/GramPEP/FactorReplacement.lean').read_text()
        self.assertIn('checkUpperCertQ_complete',src)
        self.assertIn('checkPSDFactorQ_eq_true_iff',src)
        self.assertNotIn('def checkPSDFactorQ',src)
        app=(ROOT/'LeanPEP/ActualFunction/PSDSynthesisApplications.lean').read_text()
        self.assertIn('pg_two_matrix_binding',app)
        self.assertIn('certificate_upper_of_minimizer',app)

    def cli(self,*args):
        return subprocess.run([sys.executable,str(ROOT/'tools/synthesize_psd_factors.py'),*map(str,args)],
                              text=True,capture_output=True,timeout=15)

    def test_cli_success(self):
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);i=d/'m.json';o=d/'o.json';l=d/'o.lean'
            i.write_text(s.dumps(dict(format=s.INPUT_FORMAT,dimension=2,matrix=s.matrix_json(s.exact_matrix([[2,1],[1,3]])))))
            r=self.cli('matrix',i,'--output',o,'--lean',l)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertEqual(json.loads(o.read_text())['status'],'psd');self.assertTrue(l.exists())

    def test_cli_negative_has_witness_and_nonzero_exit(self):
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);i=d/'m.json';o=d/'o.json';l=d/'o.lean'
            i.write_text(s.dumps(dict(format=s.INPUT_FORMAT,dimension=2,matrix=s.matrix_json(s.exact_matrix([[1,2],[2,1]])))))
            r=self.cli('matrix',i,'--output',o,'--lean',l)
            self.assertEqual(r.returncode,1,r.stderr)
            self.assertIn('witness_original_basis',json.loads(o.read_text()))
            self.assertIn('not_psd_real',l.read_text())

    def test_cli_bundle_preserves_source(self):
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);o=d/'b.json';l=d/'b.lean';report=d/'r.json'
            r=self.cli('bundle',ROOT/'data/fixtures/gram_external/one_step_exact.json',
                       '--output',o,'--report',report,'--lean',l)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertEqual(strip_factors(json.loads(o.read_text())),strip_factors(self.raw_bundle()))
            self.assertNotIn('native_decide',l.read_text())

    def test_cli_rejects_aliases_and_preserves_input(self):
        with tempfile.TemporaryDirectory() as d:
            i=Path(d)/'x.json';i.write_text(s.dumps(dict(format=s.INPUT_FORMAT,dimension=0,matrix=[])))
            before=i.read_bytes();r=self.cli('matrix',i,'--output',i)
            self.assertEqual(r.returncode,2);self.assertEqual(i.read_bytes(),before)

    def test_cli_bundle_failure_preserves_old_output(self):
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);i=d/'i.json';o=d/'o.json';p=d/'r.json'
            raw=self.raw_bundle();raw['upper']['dual_matrix'][0][0]={'num':-1,'den':1}
            i.write_text(s.dumps(raw));o.write_text('old output')
            r=self.cli('bundle',i,'--output',o,'--report',p)
            self.assertEqual(r.returncode,1);self.assertEqual(o.read_text(),'old output')
            self.assertFalse(json.loads(p.read_text())['bundle_emitted'])


if __name__ == '__main__':
    unittest.main()
