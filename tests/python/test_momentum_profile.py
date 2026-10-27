"""Exact, solver-free regressions for the v0.13B1 momentum pilot.

The recurrence checks are independent Python models, not a Lean interpreter.
Certificate constants and reference arrays are read from NesterovPilot.lean;
all algebra below uses Fraction.  Only Lean can check the generic Lean proofs.
"""
from __future__ import annotations

import ast
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "LeanPEP/Profiles/NesterovPilot.lean"


def rational(text: str) -> Q:
    """Parse the integer/rational arithmetic used in the exact Lean fixture."""
    text = re.sub(r"\(([-+]?\d+)\s*:\s*ℚ\)", r"\1", text.strip())
    node = ast.parse(text, mode="eval").body

    def evaluate(n: ast.AST) -> Q:
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return Q(n.value)
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd)):
            v = evaluate(n.operand)
            return -v if isinstance(n.op, ast.USub) else v
        if isinstance(n, ast.BinOp):
            a, b = evaluate(n.left), evaluate(n.right)
            if isinstance(n.op, ast.Div):
                return a / b
            if isinstance(n.op, ast.Add):
                return a + b
            if isinstance(n.op, ast.Sub):
                return a - b
            if isinstance(n.op, ast.Mult):
                return a * b
        raise ValueError(f"Unsupported exact expression: {text!r}")

    return evaluate(node)


def declaration(source: str, name: str) -> str:
    match = re.search(
        rf"(?ms)^(?:def|theorem) {re.escape(name)}\b.*?"
        rf"(?=^(?:def |theorem |@\[|end )|\Z)", source
    )
    if match is None:
        raise ValueError(f"Missing source declaration {name}")
    return match.group(0)


def vector(text: str) -> list[Q]:
    return [rational(x) for x in text.split(",")]


def zeros(n: int) -> list[list[Q]]:
    return [[Q(0) for _ in range(n)] for _ in range(n)]


def outer(u: list[Q], v: list[Q]) -> list[list[Q]]:
    return [[a * b for b in v] for a in u]


def add_scaled(dst: list[list[Q]], src: list[list[Q]], scale: Q) -> None:
    for i in range(len(dst)):
        for j in range(len(dst)):
            dst[i][j] += scale * src[i][j]


def dot(u: list[Q], v: list[Q]) -> Q:
    return sum((a * b for a, b in zip(u, v)), Q(0))


def coefficient_rows(steps: list[Q], betas: list[Q]) -> tuple[list[list[Q]], list[list[Q]]]:
    """Cumulative state and query rows; the final column is observation-only."""
    if len(steps) != len(betas):
        raise ValueError("Schedule lengths differ")
    n = len(steps)
    state, query = [[Q(0)] * (n + 1)], [[Q(0)] * (n + 1)]
    for k, (step, beta) in enumerate(zip(steps, betas)):
        x = [query[k][j] + (step if j == k else Q(0)) for j in range(n + 1)]
        y = [(1 + beta) * x[j] - beta * state[k][j] for j in range(n + 1)]
        state.append(x)
        query.append(y)
    return state, query


def output_positions(steps: list[Q], betas: list[Q]) -> list[list[Q]]:
    state, query = coefficient_rows(steps, betas)
    rows = query[:-1] + [state[-1]]
    return [[Q(0)] * (len(steps) + 2)] + [[Q(1)] + [-x for x in row] for row in rows]


def interpolation_matrix(x: list[list[Q]], g: list[list[Q]], i: int, j: int) -> list[list[Q]]:
    dx = [a - b for a, b in zip(x[i], x[j])]
    dg = [a - b for a, b in zip(g[i], g[j])]
    return [
        [-(g[j][r] * dx[c] + dx[r] * g[j][c]) / 2 - dg[r] * dg[c] / 2
         for c in range(len(dx))]
        for r in range(len(dx))
    ]


class MomentumProfileTests(unittest.TestCase):
    def test_arbitrary_schedule_causality_and_semantics(self) -> None:
        for n in range(33):
            # Negative/zero coefficients deliberately exercise structural, not
            # convergence, claims. Independent direct state/query updates below.
            steps = [Q((k * 7) % 9 - 3, k % 4 + 1) for k in range(n)]
            betas = [Q((k * 5) % 11 - 5, k % 3 + 1) for k in range(n)]
            state, query = coefficient_rows(steps, betas)
            gradients = [Q((j * 13) % 17 - 8, j % 5 + 1) for j in range(n + 1)]
            x = y = Q(7, 3)
            for k in range(n + 1):
                self.assertTrue(all(state[k][j] == query[k][j] == 0 for j in range(k, n + 1)))
                self.assertEqual(x, Q(7, 3) - dot(state[k], gradients))
                self.assertEqual(y, Q(7, 3) - dot(query[k], gradients))
                if k < n:
                    old = x
                    x = y - steps[k] * gradients[k]
                    y = x + betas[k] * (x - old)
            self.assertEqual(output_positions(steps, betas)[-1], [Q(1)] + [-a for a in state[-1]])

    def test_zero_momentum_is_unit_gd(self) -> None:
        for n in range(33):
            state, query = coefficient_rows([Q(1)] * n, [Q(0)] * n)
            for k in range(n + 1):
                self.assertEqual(state[k], [Q(int(j < k)) for j in range(n + 1)])
                self.assertEqual(query[k], state[k])

    def test_zero_horizon(self) -> None:
        self.assertEqual(output_positions([], []), [[Q(0), Q(0)], [Q(1), Q(0)]])

    def test_terminal_momentum_does_not_change_output(self) -> None:
        for n in range(1, 25):
            betas = [Q(k, k + 3) for k in range(n)]
            expected = output_positions([Q(1)] * n, betas)
            betas[-1] = Q(-79, 11)
            self.assertEqual(expected, output_positions([Q(1)] * n, betas))

    def test_exact_parser_rejects_float(self) -> None:
        with self.assertRaises(ValueError):
            rational("0.1")


class NesterovPilotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source = SOURCE.read_text(encoding="utf-8")
        text = declaration(cls.source, "pilot_positions").split(":= by")[0]
        cls.x = [vector(row) for row in re.findall(r"!\[([^\[\]]+)\]", text)]
        cls.m = len(cls.x)
        cls.g = [[Q(0)] * cls.m] + [
            [Q(int(j == i)) for j in range(cls.m)] for i in range(1, cls.m)
        ]
        text = declaration(cls.source, "pilotInterpTermsQ")
        cls.terms = [
            (rational(w), int(i), int(j)) for w, i, j in re.findall(
                r"\{\s*weight\s*:=\s*([^,]+),\s*i\s*:=\s*(\d+),\s*j\s*:=\s*(\d+)\s*\}", text
            )
        ]
        text = declaration(cls.source, "pilotDualFactorsQ")
        cls.factors = [
            (rational(w), vector(v)) for w, v in re.findall(
                r"\{\s*weight\s*:=\s*([^,]+),\s*vector\s*:=\s*!\[([^\]]+)\]\s*\}", text
            )
        ]
        primal = declaration(cls.source, "pilotPrimalQ")
        cls.values = vector(re.search(r"value\s*:=\s*!\[([^\]]+)\]", primal).group(1))
        primal_factor = declaration(cls.source, "pilotPrimalFactorQ")
        cls.v = vector(re.search(r"vector\s*:=\s*!\[([^\]]+)\]", primal_factor).group(1))
        cert = declaration(cls.source, "pilotUpperCertQ")
        cls.bound = rational(re.search(r"bound\s*:=\s*([^\n]+)", cert).group(1))
        cls.S = zeros(cls.m)
        for weight, v in cls.factors:
            add_scaled(cls.S, outer(v, v), weight)
        cls.G = outer(cls.v, cls.v)

    def identity_holds(self, *, terms=None, factors=None, bound=None, target=5, positions=None) -> bool:
        terms = self.terms if terms is None else terms
        factors = self.factors if factors is None else factors
        bound = self.bound if bound is None else bound
        x = self.x if positions is None else positions
        if any(w < 0 for w, _, _ in terms) or any(w < 0 for w, _ in factors) or bound < 0:
            return False
        rhs_f = [Q(0)] * self.m
        rhs_g = zeros(self.m)
        # Exact radius assumption coefficient is -bound * G_00.
        rhs_g[0][0] = -bound
        for w, i, j in terms:
            rhs_f[i] += w
            rhs_f[j] -= w
            add_scaled(rhs_g, interpolation_matrix(x, self.g, i, j), w)
        for w, v in factors:
            add_scaled(rhs_g, outer(v, v), w)
        target_f = [Q(0)] * self.m
        target_f[0], target_f[target] = Q(1), Q(-1)
        return rhs_g == zeros(self.m) and rhs_f == target_f

    def test_source_counts_and_exact_coefficients(self) -> None:
        self.assertEqual(self.m, 6)
        self.assertEqual(len(self.terms), 9)
        self.assertEqual(len(self.factors), 11)
        self.assertEqual(len(self.values), 6)
        self.assertEqual(len(self.v), 6)
        self.assertEqual(self.bound, Q(1, 21))
        self.assertTrue(all(len(row) == 6 for row in self.x))
        self.assertTrue(all(len(v) == 6 for _, v in self.factors))

    def test_positions_match_independent_momentum_recurrence(self) -> None:
        self.assertEqual(self.x, output_positions([Q(1)] * 4, [Q(k, k + 3) for k in range(4)]))

    def test_nonzero_historical_mix(self) -> None:
        self.assertEqual([a - b for a, b in zip(self.x[4], self.x[3])],
                         [Q(0), Q(0), -Q(1, 10), -Q(7, 5), Q(0), Q(0)])

    def test_terminal_gradient_is_observation_only(self) -> None:
        self.assertTrue(all(row[-1] == 0 for row in self.x))
        state, query = coefficient_rows([Q(1)] * 4, [Q(k, k + 3) for k in range(4)])
        self.assertNotEqual(state[-1], query[-1])
        self.assertEqual(state[4][3], Q(1))
        self.assertEqual(query[4][3], Q(3, 2))

    def test_complete_coefficient_identity(self) -> None:
        self.assertTrue(self.identity_holds())

    def test_nonnegative_weights(self) -> None:
        self.assertTrue(all(w > 0 for w, _, _ in self.terms))
        self.assertTrue(all(w > 0 for w, _ in self.factors))

    def test_symmetric_dual_matrix_and_complementarity(self) -> None:
        self.assertEqual(self.S, [list(row) for row in zip(*self.S)])
        self.assertEqual([dot(row, self.v) for row in self.S], [Q(0)] * self.m)

    def test_every_ordered_primal_interpolation(self) -> None:
        x, g = [dot(row, self.v) for row in self.x], [dot(row, self.v) for row in self.g]
        for i in range(self.m):
            for j in range(self.m):
                slack = self.values[i] - self.values[j] - g[j] * (x[i] - x[j]) - (g[i] - g[j]) ** 2 / 2
                self.assertGreaterEqual(slack, 0, (i, j, slack))
                matrix_slack = self.values[i] - self.values[j] + sum(
                    (a * b for row_a, row_b in zip(interpolation_matrix(self.x, self.g, i, j), self.G)
                     for a, b in zip(row_a, row_b)), Q(0))
                self.assertEqual(slack, matrix_slack)

    def test_radius_and_objective_attainment(self) -> None:
        self.assertEqual(self.G[0][0], Q(1))
        self.assertEqual(self.values[5] - self.values[0], self.bound)
        self.assertGreater(self.values[4] - self.values[0], self.bound)

    def test_finite_huber_sample_values(self) -> None:
        a = Q(2, 21)
        self.assertEqual(self.values[0], 0)
        for i in range(1, self.m):
            x = dot(self.x[i], self.v)
            self.assertGreaterEqual(x, a)
            self.assertEqual(self.values[i], a * x - a * a / 2)

    def test_wrong_bound_rejected_even_when_looser(self) -> None:
        self.assertFalse(self.identity_holds(bound=Q(1, 20)))

    def test_wrong_objective_rejected(self) -> None:
        self.assertFalse(self.identity_holds(target=4))

    def test_negative_interpolation_rejected(self) -> None:
        terms = list(self.terms)
        w, i, j = terms[0]
        terms[0] = (-w, i, j)
        self.assertFalse(self.identity_holds(terms=terms))

    def test_reversed_ordered_pair_rejected(self) -> None:
        terms = list(self.terms)
        w, i, j = terms[-1]
        terms[-1] = (w, j, i)
        self.assertFalse(self.identity_holds(terms=terms))

    def test_missing_dual_factor_rejected(self) -> None:
        self.assertFalse(self.identity_holds(factors=self.factors[:-1]))

    def test_corrupted_factor_entry_rejected(self) -> None:
        factors = [(w, v[:]) for w, v in self.factors]
        factors[0][1][1] += Q(1, 1000)
        self.assertFalse(self.identity_holds(factors=factors))

    def test_missing_history_in_formulation_rejected(self) -> None:
        positions = [row[:] for row in self.x]
        for row in [4, 5]:
            positions[row][2] += Q(1, 10)
        self.assertFalse(self.identity_holds(positions=positions))

    def test_using_unused_final_query_as_output_rejected(self) -> None:
        _, query = coefficient_rows([Q(1)] * 4, [Q(k, k + 3) for k in range(4)])
        positions = [row[:] for row in self.x]
        positions[-1] = [Q(1)] + [-a for a in query[-1]]
        self.assertFalse(self.identity_holds(positions=positions))


if __name__ == "__main__":
    unittest.main()
