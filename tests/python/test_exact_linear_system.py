"""D10 exact linear solver tests. No numerical solver is used."""
from dataclasses import replace
from fractions import Fraction as Q
import itertools
import random
import unittest

import solve_exact_linear_system as ls

class LinearSystemTests(unittest.TestCase):
    def test_01_empty(self):
        s=ls.System.make(0,[],[]);r=ls.solve(s,[])
        self.assertEqual(r.solution,());self.assertTrue(ls.verify_result(s,[],r))
    def test_02_all_free(self):
        s=ls.System.make(3,[],[]);self.assertEqual(ls.solve(s,[1,-2,Q(1,3)]).solution,(1,-2,Q(1,3)))
    def test_03_zero_columns_consistent(self):
        self.assertEqual(ls.solve(ls.System.make(0,[[],[]],[0,0]),[]).solution,())
    def test_04_zero_columns_inconsistent(self):
        s=ls.System.make(0,[[],[]],[0,1]);r=ls.solve(s,[])
        self.assertEqual(r.status,'inconsistent');self.assertTrue(ls.is_obstruction(s,r.obstruction))
    def test_05_unique(self):
        s=ls.System.make(2,[[1,2],[3,4]],[5,11]);self.assertEqual(ls.solve(s,[0,0]).solution,(1,2))
    def test_06_free_seed_preserved(self):
        s=ls.System.make(3,[[1,2,3]],[7]);r=ls.solve(s,[100,2,-1])
        self.assertEqual(r.free_columns,(1,2));self.assertEqual(r.solution,(6,2,-1))
    def test_07_redundant_rows(self):
        s=ls.System.make(2,[[1,1],[2,2],[0,0]],[3,6,0]);r=ls.solve(s,[0,1]);self.assertEqual(r.solution,(2,1))
    def test_08_exact_fractions(self):
        s=ls.System.make(1,[[Q(2,3)]],[Q(1,7)]);self.assertEqual(ls.solve(s,[0]).solution,(Q(3,14),))
    def test_09_rank_zero(self):
        s=ls.System.make(2,[[0,0]],[0]);r=ls.solve(s,[1,2]);self.assertEqual(r.pivot_columns,())
    def test_10_pivot_row_swap(self):
        s=ls.System.make(2,[[0,1],[1,0]],[4,3]);self.assertEqual(ls.solve(s,[0,0]).solution,(3,4))
    def test_11_obstruction(self):
        s=ls.System.make(1,[[1],[2]],[1,3]);r=ls.solve(s,[0]);self.assertTrue(ls.is_obstruction(s,r.obstruction))
    def test_12_wrong_solution(self):
        s=ls.System.make(1,[[1]],[1]);r=ls.solve(s,[0]);self.assertFalse(ls.verify_result(s,[0],replace(r,solution=(Q(2),))))
    def test_13_wrong_obstruction(self):
        s=ls.System.make(1,[[1],[1]],[1,2]);self.assertFalse(ls.is_obstruction(s,[1,1]))
    def test_14_float_rejected(self):
        with self.assertRaises(ValueError):ls.System.make(1,[[.1]],[0])
    def test_15_boolean_rejected(self):
        with self.assertRaises(ValueError):ls.System.make(1,[[True]],[0])
    def test_16_shape_rejected(self):
        with self.assertRaises(ValueError):ls.System.make(2,[[1]],[0])
        with self.assertRaises(ValueError):ls.System.make(2,[[1,2]],[])
    def test_17_seed_shape_rejected(self):
        with self.assertRaises(ValueError):ls.solve(ls.System.make(2,[],[]),[0])
    def test_18_deterministic(self):
        s=ls.System.make(3,[[1,2,3],[4,5,6]],[7,8]);self.assertEqual(ls.solve(s,[1,2,3]),ls.solve(s,[1,2,3]))
    def test_19_independent_sympy_rank(self):
        import sympy as sp
        rng=random.Random(1010)
        for _ in range(60):
            nr,nc=rng.randrange(1,5),rng.randrange(1,5)
            A=[[rng.randrange(-2,3) for _ in range(nc)] for _ in range(nr)]
            b=[rng.randrange(-2,3) for _ in range(nr)]
            s=ls.System.make(nc,A,b);r=ls.solve(s,[Q(1,3)]*nc)
            consistent=sp.Matrix(A).rank()==sp.Matrix([row+[q] for row,q in zip(A,b)]).rank()
            self.assertEqual(r.status=='solution',consistent)
            self.assertTrue(ls.verify_result(s,[Q(1,3)]*nc,r))
    def test_20_negative_solution_not_clipped(self):
        s=ls.System.make(1,[[1]],[-1]);self.assertEqual(ls.solve(s,[0]).solution,(Q(-1),))
    def test_21_wrong_witness_length(self):
        self.assertFalse(ls.is_obstruction(ls.System.make(1,[[0]],[1]),[]))
    def test_22_duplicate_columns(self):
        s=ls.System.make(2,[[1,1]],[1]);self.assertEqual(ls.solve(s,[0,Q(1,4)]).solution,(Q(3,4),Q(1,4)))
    def test_23_row_permutation(self):
        A=[[2,3],[5,7]];b=[7,17]
        self.assertEqual(ls.solve(ls.System.make(2,A,b),[0,0]).solution,
            ls.solve(ls.System.make(2,A[::-1],b[::-1]),[0,0]).solution)
    def test_24_tiny_nonzero_not_zero(self):
        tiny=Q(1,10**100);s=ls.System.make(1,[[tiny]],[1]);self.assertEqual(ls.solve(s,[0]).solution,(1/tiny,))
    def test_25_exhaustive_single_equation(self):
        for a,b,c in itertools.product(range(-2,3),repeat=3):
            s=ls.System.make(2,[[a,b]],[c]);r=ls.solve(s,[3,5])
            self.assertEqual(r.status=='solution',bool(a or b or not c));self.assertTrue(ls.verify_result(s,[3,5],r))
    def test_26_public_dataclass_revalidated(self):
        with self.assertRaises(ValueError):ls.solve(ls.System(1,((0.1,),),(Q(1),)),[0])
    def test_27_free_value_change_rejected(self):
        s=ls.System.make(2,[[1,0]],[1]);r=ls.solve(s,[0,2])
        self.assertFalse(ls.verify_result(s,[0,2],replace(r,solution=(Q(1),Q(3)))))
    def test_28_nontrivial_witness_original_rows(self):
        s=ls.System.make(2,[[1,2],[2,4],[4,8]],[3,6,13]);r=ls.solve(s,[0,0])
        self.assertTrue(ls.is_obstruction(s,r.obstruction));self.assertNotEqual(r.obstruction,(0,0,1))

    def test_29_independent_check_rejects_inexact_numbers(self):
        s=ls.System.make(1,[[1]],[1]);self.assertFalse(ls.is_solution(s,[1.0]))
        self.assertFalse(ls.is_solution(s,[True]))
        self.assertFalse(ls.is_solution(ls.System(1,(),(Q(1),)),[1]))

if __name__=='__main__':unittest.main()
