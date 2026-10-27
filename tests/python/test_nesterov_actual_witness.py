"""Exact regressions for the B3 actual Huber witness and oracle agreement.

This is independent Fraction arithmetic, NOT a Lean interpreter.  Constants
and advertised reference states are read from the new Lean source.  Existing
B1 primal/certificate constants are read separately from the unchanged fixture.
Analytic regularity and IsGreatest are Lean obligations, not numerical claims.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_momentum_actual as b2
from tests.python import test_momentum_profile as b1

SOURCE = Path(__file__).resolve().parents[2] / "LeanPEP/ActualFunction/NesterovPilotWitness.lean"


def source_table(source: str, theorem: str, field: str) -> list[Q]:
    header = b1.declaration(source, theorem).split(":= by", 1)[0]
    pairs = re.findall(rf"{field}\s+(\d+)\s*=\s*(\d+(?:\s*/\s*\d+)?)", header)
    if [int(k) for k, _ in pairs] != list(range(5)):
        raise ValueError(f"Unexpected source table for {field}")
    return [b1.rational(v) for _, v in pairs]


class NesterovActualWitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source = SOURCE.read_text(encoding="utf-8")
        threshold = re.search(r"^def threshold : ℝ := ([^\n]+)$", cls.source, re.M)
        if threshold is None:
            raise ValueError("Missing exact threshold")
        cls.a = b1.rational(threshold.group(1))
        cls.steps = [Q(1)] * 4
        cls.betas = [Q(k, k+3) for k in range(4)]
        f, g = b2.huber(cls.a)
        # Prevent closures stored on the test class from binding an extra self.
        cls.f, cls.g = staticmethod(f), staticmethod(g)
        cls.states, cls.queries = b2.actual_run(cls.steps, cls.betas, cls.g, [Q(1)])
        cls.ref_states, cls.ref_queries = b2.actual_run(
            cls.steps, cls.betas, lambda _: [cls.a], [Q(1)])
        cls.source_x = source_table(cls.source, "reference_state_values", "referenceState")
        cls.source_y = source_table(cls.source, "reference_query_values", "referenceQuery")
        cls.datum = b2.datum(cls.steps, cls.betas, cls.f, cls.g, [Q(0)], [Q(1)])
        old = b1.SOURCE.read_text(encoding="utf-8")
        p = b1.declaration(old, "pilotPrimalQ")
        v = re.search(r"value\s*:=\s*!\[([^\]]+)\]", p)
        factor = re.search(r"vector\s*:=\s*!\[([^\]]+)\]", b1.declaration(old, "pilotPrimalFactorQ"))
        if v is None or factor is None:
            raise ValueError("Missing B1 primal constants")
        cls.primal_values = b1.vector(v.group(1))
        cls.primal_factor = b1.vector(factor.group(1))

    def test_exact_threshold(self) -> None:
        self.assertEqual(self.a, Q(2, 21))
        self.assertGreater(self.a, 0)

    def test_reference_states_match_lean_statement(self) -> None:
        self.assertEqual([x[0] for x in self.ref_states], self.source_x)

    def test_reference_queries_match_lean_statement(self) -> None:
        self.assertEqual([y[0] for y in self.ref_queries], self.source_y)

    def test_all_reference_queries_are_on_constant_branch(self) -> None:
        for y in self.ref_queries:
            self.assertGreaterEqual(y[0], self.a)
            self.assertEqual(self.g(y), [self.a])

    def test_both_actual_sequences_equal_reference(self) -> None:
        self.assertEqual(self.states, self.ref_states)
        self.assertEqual(self.queries, self.ref_queries)

    def test_stationary_global_minimum_samples(self) -> None:
        self.assertEqual(self.g([Q(0)]), [Q(0)])
        self.assertEqual(self.f([Q(0)]), 0)
        for x in [Q(k, 21) for k in range(-42, 43)]:
            self.assertGreaterEqual(self.f([x]), self.f([Q(0)]))

    def test_actual_attainment(self) -> None:
        self.assertEqual(self.states[-1], [Q(23, 42)])
        self.assertEqual(self.f(self.states[-1]) - self.f([Q(0)]), Q(1, 21))

    def test_actual_datum_matches_unchanged_b1_primal(self) -> None:
        self.assertEqual(self.datum.values, self.primal_values)
        self.assertEqual([v[0] for v in self.datum.base], self.primal_factor)
        self.assertEqual(self.datum.gram, b1.outer(self.primal_factor, self.primal_factor))

    def test_all_36_actual_ordered_interpolations(self) -> None:
        for x in self.datum.samples:
            for y in self.datum.samples:
                self.assertGreaterEqual(b2.actual_slack(self.f, self.g, x, y), 0)

    def test_exact_complementarity_for_original_certificate(self) -> None:
        terms, factors = b2.pilot_constants()
        for weight, i, j in terms:
            self.assertGreater(weight, 0)
            self.assertEqual(b2.actual_slack(self.f, self.g,
                self.datum.samples[i], self.datum.samples[j]), 0)
        for weight, v in factors:
            self.assertGreater(weight, 0)
            self.assertEqual(b2.realize(v, self.datum.base), [Q(0)])
        self.assertEqual(self.datum.gram[0][0], 1)

    def test_reference_constant_field_is_not_a_stationary_witness(self) -> None:
        self.assertNotEqual([self.a], self.g([Q(0)]))

    def test_terminal_state_and_query_are_distinct(self) -> None:
        self.assertEqual(self.queries[-1], [Q(10, 21)])
        self.assertNotEqual(self.states[-1], self.queries[-1])
        self.assertEqual(self.f(self.queries[-1]) - self.f([Q(0)]), Q(2, 49))
        self.assertNotEqual(self.f(self.queries[-1]), Q(1, 21))

    def test_threshold_mutation_does_not_attain_same_bound(self) -> None:
        for a in (Q(0), Q(1, 10), Q(1, 8)):
            f, g = b2.huber(a)
            states, _ = b2.actual_run(self.steps, self.betas, g, [Q(1)])
            self.assertNotEqual(f(states[-1])-f([Q(0)]), Q(1, 21))

    def test_wrong_target_is_not_the_four_step_bound(self) -> None:
        self.assertEqual(self.f(self.queries[3]), Q(25, 441))
        self.assertGreater(self.f(self.queries[3]), Q(1, 21))

    def test_huber_join_values_and_gradient(self) -> None:
        self.assertEqual(self.f([self.a]), self.a*self.a/2)
        self.assertEqual(self.a*self.a - self.a*self.a/2, self.f([self.a]))
        self.assertEqual(self.g([self.a]), [self.a])
        self.assertEqual(self.g([self.a-Q(1, 1000)]), [self.a-Q(1, 1000)])
        self.assertEqual(self.g([self.a+Q(1, 1000)]), [self.a])


class OracleAgreementTests(unittest.TestCase):
    def test_reference_query_agreement_arbitrary_schedules(self) -> None:
        for dim in (1, 2, 5):
            initial = [Q(j+1, 5) for j in range(dim)]
            _, g = b2.quadratic([Q(0)]*dim, [Q(j+1, dim+2) for j in range(dim)])
            for n in range(13):
                steps = [Q((7*k)%9-3, k%4+1) for k in range(n)]
                betas = [Q((5*k)%11-5, k%3+1) for k in range(n)]
                states, queries = b2.actual_run(steps, betas, g, initial)
                queried = {tuple(y) for y in queries[:-1]}

                def other(x: b2.Vec) -> b2.Vec:
                    return g(x) if tuple(x) in queried else [Q(71)]*dim

                self.assertEqual(b2.actual_run(steps, betas, other, initial), (states, queries))

    def test_terminal_gradient_agreement_is_not_required(self) -> None:
        def reference(_: b2.Vec) -> b2.Vec:
            return [Q(1)]

        def other(x: b2.Vec) -> b2.Vec:
            return [Q(1) if x == [Q(0)] else Q(7)]

        expected = b2.actual_run([Q(1)], [Q(0)], reference, [Q(0)])
        got = b2.actual_run([Q(1)], [Q(0)], other, [Q(0)])
        self.assertEqual(expected, got)
        final = expected[0][-1]
        self.assertNotEqual(reference(final), other(final))

    def test_agreement_on_states_cannot_replace_queries(self) -> None:
        _, g = b2.quadratic([Q(0)], [Q(1, 3)])
        steps, betas = [Q(1)]*3, [Q(k, k+3) for k in range(3)]
        states, queries = b2.actual_run(steps, betas, g, [Q(1)])
        changed = queries[2]
        self.assertNotIn(changed, states[:3])

        def other(x: b2.Vec) -> b2.Vec:
            return b2.add(g(x), [Q(1)]) if x == changed else g(x)

        for x in states[:3]:
            self.assertEqual(other(x), g(x))
        got = b2.actual_run(steps, betas, other, [Q(1)])
        self.assertNotEqual(got[0][-1], states[-1])

    def test_missing_last_required_query_breaks_agreement(self) -> None:
        g = lambda _: [Q(1)]
        steps, betas = [Q(1)]*4, [Q(0)]*4
        states, queries = b2.actual_run(steps, betas, g, [Q(0)])

        def other(x: b2.Vec) -> b2.Vec:
            return [Q(2)] if x == queries[3] else g(x)

        for y in queries[:3]:
            self.assertEqual(other(y), g(y))
        got = b2.actual_run(steps, betas, other, [Q(0)])
        self.assertNotEqual(got[0][-1], states[-1])

    def test_zero_horizon_never_calls_either_oracle(self) -> None:
        def forbidden(_: b2.Vec) -> b2.Vec:
            raise AssertionError("No oracle call is allowed at zero horizon")

        self.assertEqual(b2.actual_run([], [], forbidden, [Q(3)]), ([[Q(3)]], [[Q(3)]]))


if __name__ == "__main__":
    unittest.main()
