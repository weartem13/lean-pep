#!/usr/bin/env python3
"""D11: exact rational feasibility of A x = b, lower <= x <= upper.

A phase-I simplex search (least-index entering variable and Bland tie-breaking)
may choose different free-variable values from a seed. Every proposed solution
or Farkas obstruction is rechecked against the ORIGINAL input. No floating
arithmetic, tolerances, nearest-point claim, or denominator-bound search is used.
A pivot limit returns 'limit', never an infeasibility claim.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence

import solve_exact_linear_system as lin


@dataclass(frozen=True)
class BoxSystem:
    system: lin.System
    lower: tuple[Q, ...]
    upper: tuple[Q, ...]

    @classmethod
    def make(cls, system: lin.System, lower: Sequence[Q | int],
             upper: Sequence[Q | int]) -> 'BoxSystem':
        s = lin.System.make(system.columns, system.matrix, system.rhs)
        lo, hi = tuple(map(lin.rational, lower)), tuple(map(lin.rational, upper))
        if len(lo) != s.columns or len(hi) != s.columns:
            raise ValueError('box bounds must match the number of columns')
        # Empty intervals are well-formed input; return an exact obstruction.
        return cls(s, lo, hi)


@dataclass(frozen=True)
class Obstruction:
    equality: tuple[Q, ...]  # unrestricted y
    lower: tuple[Q, ...]     # nonnegative nu
    upper: tuple[Q, ...]     # nonnegative mu


@dataclass(frozen=True)
class Result:
    status: str
    solution: tuple[Q, ...] | None
    obstruction: Obstruction | None
    pivots: int
    seed_used: bool = False


def is_solution(s: BoxSystem, x: Sequence[Q | int]) -> bool:
    try:
        s = BoxSystem.make(s.system, s.lower, s.upper)
        x = tuple(map(lin.rational, x))
    except (ValueError, TypeError, AttributeError):
        return False
    return lin.is_solution(s.system, x) and all(
        lo <= v <= hi for lo, v, hi in zip(s.lower, x, s.upper))


def obstruction_value(s: BoxSystem, w: Obstruction) -> Q:
    return (sum((v*b for v,b in zip(w.equality, s.system.rhs)), Q(0))
            + sum((mu*hi-nu*lo for mu,hi,nu,lo in
                   zip(w.upper,s.upper,w.lower,s.lower)), Q(0)))


def is_obstruction(s: BoxSystem, w: Obstruction) -> bool:
    """y^T A + mu - nu = 0; mu,nu >= 0; y^T b + mu^T u - nu^T l < 0."""
    try:
        s = BoxSystem.make(s.system, s.lower, s.upper)
        w = Obstruction(*(tuple(map(lin.rational, v)) for v in
                          (w.equality, w.lower, w.upper)))
    except (ValueError, TypeError, AttributeError):
        return False
    r, c = len(s.system.rhs), s.system.columns
    return (len(w.equality) == r and len(w.lower) == c and len(w.upper) == c
        and all(v >= 0 for v in w.lower+w.upper)
        and all(sum((w.equality[i]*s.system.matrix[i][j] for i in range(r)), Q(0))
                + w.upper[j] - w.lower[j] == 0 for j in range(c))
        and obstruction_value(s, w) < 0)


def verify_result(s: BoxSystem, result: Result) -> bool:
    if type(result.pivots) is not int or result.pivots < 0:
        return False
    if result.status == 'feasible':
        return (result.solution is not None and result.obstruction is None
                and is_solution(s, result.solution))
    if result.status == 'infeasible':
        return (result.solution is None and result.obstruction is not None
                and is_obstruction(s, result.obstruction))
    return (result.status == 'limit' and result.solution is None
            and result.obstruction is None)


def _add_scaled(a: dict[int, Q], b: dict[int, Q], scale: Q) -> None:
    if not scale:
        return
    for j, v in b.items():
        new = a.get(j, Q(0)) + scale*v
        if new:
            a[j] = new
        else:
            a.pop(j, None)


def solve(s: BoxSystem, seed: Sequence[Q | int] | None = None,
          *, max_pivots: int = 10000) -> Result:
    s = BoxSystem.make(s.system, s.lower, s.upper)
    if type(max_pivots) is not int or max_pivots < 0:
        raise ValueError('max_pivots must be a nonnegative integer')
    r, c = len(s.system.rhs), s.system.columns
    if seed is not None:
        seed = tuple(map(lin.rational, seed))
        if len(seed) != c:
            raise ValueError('seed length differs from the number of columns')
        if is_solution(s, seed):
            return Result('feasible', seed, None, 0, True)
    bad = next((j for j in range(c) if s.lower[j] > s.upper[j]), None)
    if bad is not None:
        unit = tuple(Q(j == bad) for j in range(c))
        w = Obstruction((Q(0),)*r, unit, unit)
        out = Result('infeasible', None, w, 0)
        if not verify_result(s, out):
            raise ArithmeticError('empty-interval obstruction failed recheck')
        return out

    # x = l + z. Tableau variables: z[c], cap slacks[c], artificials[r].
    # Equality rows are sign-flipped only internally so all initial RHS >= 0.
    signs: list[Q] = []
    rows: list[dict[int, Q]] = []
    rhs: list[Q] = []
    basis: list[int] = []
    for i in range(r):
        b = s.system.rhs[i] - sum((a*lo for a,lo in
                                  zip(s.system.matrix[i],s.lower)), Q(0))
        sign = Q(1) if b >= 0 else Q(-1)
        signs.append(sign)
        row = {j: sign*a for j,a in enumerate(s.system.matrix[i]) if a}
        row[2*c+i] = Q(1)
        rows.append(row); rhs.append(sign*b); basis.append(2*c+i)
    for j in range(c):
        rows.append({j: Q(1), c+j: Q(1)})
        rhs.append(s.upper[j]-s.lower[j]); basis.append(c+j)
    # Track row combinations to recover an ORIGINAL-system Farkas witness.
    combinations = [{i: Q(1)} for i in range(r+c)]
    reduced = {2*c+i: Q(-1) for i in range(r)}
    dual = {i: Q(-1) for i in range(r)}
    objective = -sum(rhs[:r], Q(0))
    for row in rows[:r]:
        _add_scaled(reduced, row, Q(1))

    pivots = 0
    while True:
        entering = min((j for j,v in reduced.items() if v > 0), default=None)
        if entering is None or objective == 0:
            break
        if pivots >= max_pivots:
            return Result('limit', None, None, pivots)
        eligible = [(rhs[i]/rows[i][entering], basis[i], i)
                    for i in range(r+c) if rows[i].get(entering, Q(0)) > 0]
        if not eligible:
            raise ArithmeticError('phase-I objective unexpectedly unbounded')
        _, _, leaving = min(eligible)
        divisor = rows[leaving][entering]
        rows[leaving] = {j:v/divisor for j,v in rows[leaving].items()}
        rhs[leaving] /= divisor
        combinations[leaving] = {j:v/divisor for j,v in combinations[leaving].items()}
        pr, pc, pb = rows[leaving], combinations[leaving], rhs[leaving]
        for i in range(r+c):
            if i == leaving:
                continue
            a = rows[i].get(entering, Q(0))
            if a:
                _add_scaled(rows[i], pr, -a)
                rhs[i] -= a*pb
                _add_scaled(combinations[i], pc, -a)
        gain = reduced[entering]
        _add_scaled(reduced, pr, -gain)
        _add_scaled(dual, pc, gain)
        objective += gain*pb
        basis[leaving] = entering
        pivots += 1
        if objective > 0 or any(b < 0 for b in rhs):
            raise ArithmeticError('phase-I invariant failure')

    if objective == 0:
        z = [Q(0)]*c
        for i,j in enumerate(basis):
            if j < c:
                z[j] = rhs[i]
        x = tuple(lo+v for lo,v in zip(s.lower,z))
        out = Result('feasible', x, None, pivots)
    else:
        y = tuple(dual.get(i,Q(0))*signs[i] for i in range(r))
        mu = tuple(dual.get(r+j,Q(0)) for j in range(c))
        nu = tuple(sum((y[i]*s.system.matrix[i][j] for i in range(r)),Q(0))+mu[j]
                   for j in range(c))
        out = Result('infeasible', None, Obstruction(y,nu,mu), pivots)
    if not verify_result(s, out):
        raise ArithmeticError('phase-I output failed independent original-system recheck')
    return out
