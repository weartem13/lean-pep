#!/usr/bin/env python3
"""D10: exact affine completion with an independently checkable result.

Input coefficients must already be rational. Gauss--Jordan elimination is
untrusted: solutions and rational inconsistency witnesses are rechecked against
ALL entries of the original system. Free variables keep their supplied seed
values. This is not a nonnegative solver, PSD solver, or nearest-point method.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence


def rational(x: Q | int) -> Q:
    if type(x) is int or isinstance(x, Q):
        return Q(x)
    raise ValueError('expected an exact integer/Fraction (not Boolean or float)')


@dataclass(frozen=True)
class System:
    columns: int
    matrix: tuple[tuple[Q, ...], ...]
    rhs: tuple[Q, ...]

    @classmethod
    def make(cls, columns: int, matrix: Sequence[Sequence[Q | int]],
             rhs: Sequence[Q | int]) -> 'System':
        if type(columns) is not int or columns < 0:
            raise ValueError('columns must be a nonnegative integer')
        A = tuple(tuple(rational(v) for v in row) for row in matrix)
        b = tuple(rational(v) for v in rhs)
        if len(A) != len(b) or any(len(row) != columns for row in A):
            raise ValueError('inconsistent system dimensions')
        return cls(columns, A, b)


@dataclass(frozen=True)
class Result:
    status: str
    solution: tuple[Q, ...] | None
    obstruction: tuple[Q, ...] | None
    pivot_columns: tuple[int, ...]
    free_columns: tuple[int, ...]


def is_solution(s: System, x: Sequence[Q]) -> bool:
    try:
        s = System.make(s.columns, s.matrix, s.rhs)
        x = tuple(rational(v) for v in x)
    except (ValueError, TypeError):
        return False
    return len(x) == s.columns and all(
        sum((a * v for a, v in zip(row, x)), Q(0)) == b
        for row, b in zip(s.matrix, s.rhs))


def is_obstruction(s: System, y: Sequence[Q]) -> bool:
    """y^T A = 0 and y^T b != 0; proves inconsistency, not PEP infeasibility."""
    try:
        s = System.make(s.columns, s.matrix, s.rhs)
        y = tuple(rational(v) for v in y)
    except (ValueError, TypeError):
        return False
    return len(y) == len(s.rhs) and all(
        sum((y[i] * s.matrix[i][j] for i in range(len(y))), Q(0)) == 0
        for j in range(s.columns)) and sum(
        (a * b for a, b in zip(y, s.rhs)), Q(0)) != 0


def verify_result(s: System, seed: Sequence[Q], r: Result) -> bool:
    if r.status == 'inconsistent':
        return r.solution is None and r.obstruction is not None and is_obstruction(s, r.obstruction)
    if r.status != 'solution' or r.solution is None or r.obstruction is not None:
        return False
    return (is_solution(s, r.solution) and len(seed) == s.columns
        and sorted(r.pivot_columns + r.free_columns) == list(range(s.columns))
        and all(r.solution[j] == seed[j] for j in r.free_columns))


def solve(s: System, seed: Sequence[Q | int]) -> Result:
    # Revalidate public dataclass instances; no zip-based truncation of inputs.
    s = System.make(s.columns, s.matrix, s.rhs)
    start = tuple(rational(x) for x in seed)
    if len(start) != s.columns:
        raise ValueError('seed length differs from number of unknowns')
    n = len(s.rhs)
    A = [list(row) + [b] for row, b in zip(s.matrix, s.rhs)]
    # Sparse row-operation witnesses avoid a dense n-by-n auxiliary matrix.
    combinations: list[dict[int, Q]] = [{i: Q(1)} for i in range(n)]
    pivots: list[int] = []
    rank = 0
    for j in range(s.columns):
        chosen = next((i for i in range(rank, n) if A[i][j]), None)
        if chosen is None:
            continue
        A[rank], A[chosen] = A[chosen], A[rank]
        combinations[rank], combinations[chosen] = combinations[chosen], combinations[rank]
        d = A[rank][j]
        A[rank] = [v / d for v in A[rank]]
        combinations[rank] = {i: v / d for i, v in combinations[rank].items()}
        for i in range(n):
            if i == rank or not A[i][j]:
                continue
            a = A[i][j]
            A[i] = [v - a * w for v, w in zip(A[i], A[rank])]
            for k, w in combinations[rank].items():
                v = combinations[i].get(k, Q(0)) - a * w
                if v:
                    combinations[i][k] = v
                else:
                    combinations[i].pop(k, None)
        pivots.append(j)
        rank += 1
        if rank == n:
            break
    free = tuple(j for j in range(s.columns) if j not in pivots)
    bad = next((i for i in range(n) if all(a == 0 for a in A[i][:-1]) and A[i][-1]), None)
    if bad is not None:
        witness = tuple(combinations[bad].get(i, Q(0)) for i in range(n))
        result = Result('inconsistent', None, witness, tuple(pivots), free)
    else:
        x = list(start)
        for i, j in enumerate(pivots):
            x[j] = A[i][-1] - sum((A[i][k] * x[k] for k in free), Q(0))
        result = Result('solution', tuple(x), None, tuple(pivots), free)
    if not verify_result(s, start, result):
        raise ArithmeticError('exact row-reduction output failed original-system recheck')
    return result
