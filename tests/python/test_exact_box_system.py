"""D11 exact box feasibility, original-system Farkas checks and boundaries."""
from dataclasses import replace
from fractions import Fraction as Q
import itertools
import random
import unittest
import sympy as sp
import solve_exact_linear_system as lin
import solve_exact_box_system as box


def problem(A,b,l,u):return box.BoxSystem.make(lin.System.make(len(l),A,b),l,u)


def vertices_feasible(s):
    """Independent exact bounded-polytope vertex enumeration, for small tests."""
    c=s.system.columns
    if any(l>u for l,u in zip(s.lower,s.upper)):return False
    if c==0:return all(b==0 for b in s.system.rhs)
    rows=[tuple(row)+(b,) for row,b in zip(s.system.matrix,s.system.rhs)]
    for j in range(c):
        for b in (s.lower[j],s.upper[j]):rows.append(tuple(Q(i==j) for i in range(c))+(b,))
    for chosen in itertools.combinations(rows,c):
        A=sp.Matrix([[sp.Rational(a.numerator,a.denominator) for a in row[:-1]] for row in chosen])
        if A.det()==0:continue
        b=sp.Matrix([sp.Rational(row[-1].numerator,row[-1].denominator) for row in chosen])
        v=A.inv()*b
        x=tuple(Q(int(a.p),int(a.q)) for a in v)
        if box.is_solution(s,x):return True
    return False


class BoxTests(unittest.TestCase):
    def test_01_coupled_free_variable(self):
        s=problem([[1,1]],[1],[0,0],[1,1]);old=lin.solve(s.system,[2,-1])
        self.assertEqual(old.solution,(2,-1));self.assertFalse(box.is_solution(s,old.solution))
        r=box.solve(s,old.solution);self.assertEqual(r.solution,(1,0));self.assertTrue(box.verify_result(s,r))
    def test_02_nonnegative_obstruction(self):
        s=problem([[1,1]],[3],[0,0],[1,1]);r=box.solve(s)
        self.assertEqual(r.status,'infeasible');self.assertEqual(box.obstruction_value(s,r.obstruction),-1)
    def test_03_affinely_inconsistent(self):
        s=problem([[1],[1]],[0,1],[-2],[2]);r=box.solve(s);self.assertTrue(box.is_obstruction(s,r.obstruction))
    def test_04_negative_box_entries(self):
        s=problem([[1,1]],[-3],[-3,-3],[-1,-1]);r=box.solve(s);self.assertTrue(box.is_solution(s,r.solution))
    def test_05_empty_interval(self):
        s=problem([],[],[2],[1]);r=box.solve(s);self.assertTrue(box.is_obstruction(s,r.obstruction));self.assertEqual(r.pivots,0)
    def test_06_zero_dim_feasible(self):
        self.assertEqual(box.solve(problem([[]],[0],[],[])).solution,())
    def test_07_zero_dim_infeasible(self):
        s=problem([[]],[1],[],[]);self.assertTrue(box.is_obstruction(s,box.solve(s).obstruction))
    def test_08_completely_empty(self):self.assertEqual(box.solve(problem([],[],[],[])).solution,())
    def test_09_no_equalities(self):
        s=problem([],[],[-1,2],[1,3]);self.assertTrue(box.is_solution(s,box.solve(s).solution))
    def test_10_duplicate_equalities(self):
        s=problem([[1,1],[2,2]],[1,2],[0,0],[1,1]);self.assertTrue(box.is_solution(s,box.solve(s).solution))
    def test_11_singletons(self):
        s=problem([[1,1]],[3],[1,2],[1,2]);self.assertEqual(box.solve(s).solution,(1,2))
    def test_12_degenerate_zero_rhs(self):
        s=problem([[1,1],[1,0]],[0,0],[0,0],[1,1]);self.assertEqual(box.solve(s).solution,(0,0))
    def test_13_exact_tiny_infeasibility(self):
        tiny=Q(1,10**60);s=problem([[1]],[-tiny],[0],[1]);r=box.solve(s)
        self.assertEqual(r.status,'infeasible');self.assertLess(box.obstruction_value(s,r.obstruction),0)
    def test_14_no_denominator_guarantee(self):
        s=problem([[3]],[1],[0],[1]);self.assertEqual(box.solve(s).solution,(Q(1,3),))
    def test_15_feasible_seed_retained(self):
        s=problem([[1,1]],[1],[0,0],[1,1]);r=box.solve(s,[Q(1,3),Q(2,3)])
        self.assertTrue(r.seed_used);self.assertEqual(r.pivots,0)
    def test_16_zero_limit_unknown(self):
        s=problem([[1,1]],[1],[0,0],[1,1]);r=box.solve(s,max_pivots=0)
        self.assertEqual(r.status,'limit');self.assertIsNone(r.obstruction);self.assertTrue(box.verify_result(s,r))
    def test_17_limit_does_not_stop_verified_seed(self):
        s=problem([[1]],[1],[0],[1]);self.assertEqual(box.solve(s,[1],max_pivots=0).status,'feasible')
    def test_18_invalid_limit(self):
        for n in [-1,True,0.5]:
            with self.assertRaises(ValueError):box.solve(problem([],[],[],[]),max_pivots=n)
    def test_19_seed_length(self):
        with self.assertRaises(ValueError):box.solve(problem([],[],[0],[1]),[])
    def test_20_bounds_length(self):
        with self.assertRaises(ValueError):problem([[1]],[0],[0],[])
    def test_21_float_boolean_rejected(self):
        for q in [0.5,True,'1/2']:
            with self.assertRaises(ValueError):problem([[1]],[0],[q],[1])
    def test_22_wrong_solution(self):self.assertFalse(box.is_solution(problem([[1]],[0],[0],[1]),[1]))
    def test_23_solution_truncation_rejected(self):self.assertFalse(box.is_solution(problem([[1]],[0],[0],[1]),[]))
    def test_24_witness_sign_rejected(self):
        s=problem([[1]],[2],[0],[1]);w=box.solve(s).obstruction
        self.assertFalse(box.is_obstruction(s,replace(w,upper=(-1,))))
    def test_25_witness_rhs_rejected(self):
        s=problem([[1]],[2],[0],[1]);w=box.solve(s).obstruction
        self.assertFalse(box.is_obstruction(problem([[1]],[0],[0],[1]),w))
    def test_26_witness_length_rejected(self):
        s=problem([[1]],[2],[0],[1]);w=box.solve(s).obstruction
        self.assertFalse(box.is_obstruction(s,replace(w,equality=())))
    def test_27_zero_margin_not_obstruction(self):
        s=problem([[1]],[1],[0],[1]);self.assertFalse(box.is_obstruction(s,box.Obstruction((-1,),(0,),(1,))))
    def test_28_malicious_result_status(self):
        s=problem([[1]],[1],[0],[1]);r=box.Result('infeasible',(1,),None,0)
        self.assertFalse(box.verify_result(s,r))
    def test_29_input_immutable(self):
        s=problem([[1,2]],[2],[0,0],[2,2]);before=repr(s);box.solve(s);self.assertEqual(repr(s),before)
    def test_30_deterministic(self):
        s=problem([[1,1,1]],[1],[0,0,0],[1,1,1]);self.assertEqual(box.solve(s),box.solve(s))
    def test_31_exhaustive_two_var_vertex_reference(self):
        for a,b,d in itertools.product(range(-2,3),repeat=3):
            s=problem([[a,b]],[d],[0,0],[1,1]);r=box.solve(s)
            self.assertTrue(box.verify_result(s,r));self.assertEqual(r.status=='feasible',vertices_feasible(s))
    def test_32_random_three_var_exact_vertex_reference(self):
        rng=random.Random(20260926)
        for _ in range(45):
            A=[[rng.randint(-2,2) for _ in range(3)] for __ in range(2)]
            s=problem(A,[rng.randint(-3,3) for _ in range(2)],[-1,-1,0],[2,1,2]);r=box.solve(s)
            self.assertTrue(box.verify_result(s,r));self.assertEqual(r.status=='feasible',vertices_feasible(s))
    def test_33_row_scaling(self):
        s=problem([[2,4],[-3,-6]],[2,-3],[0,0],[2,2]);self.assertEqual(box.solve(s).status,'feasible')
    def test_34_zero_column_free_seed(self):
        s=problem([[1,0]],[1],[0,0],[2,1]);r=box.solve(s,[1,-1]);self.assertEqual(r.solution,(1,0))
    def test_35_negative_rhs_and_lower_shift(self):
        s=problem([[1,-2]],[-2],[-3,-1],[0,2]);self.assertTrue(box.is_solution(s,box.solve(s).solution))
    def test_36_farkas_slack_identity(self):
        # Arbitrary stationarity vector, not an obstruction, on a feasible point.
        s=problem([[1,2]],[3],[0,0],[2,2]);x=(1,1);w=box.Obstruction((1,),(3,5),(2,3))
        lhs=box.obstruction_value(s,w)
        rhs=sum((nu*(v-l)+mu*(u-v) for nu,mu,v,l,u in zip(w.lower,w.upper,x,s.lower,s.upper)),Q(0))
        self.assertEqual(lhs,rhs)

if __name__=='__main__':unittest.main()
