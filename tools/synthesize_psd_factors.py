#!/usr/bin/env python3
"""Untrusted, square-root-free rational PSD certificate synthesis (v0.13D1).

No floats, tolerances, matrix repair or solver calls. Both primal and dual
matrices use exactly the same routine. Positive output is an existing
PSDFactorCertQ candidate; negative output is an original-coordinate vector
whose quadratic value is strictly negative, or an exact asymmetry. Python
checks are diagnostics, not Lean acceptance and not full PEP feasibility.
"""
from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import dataclass, replace
from fractions import Fraction
from pathlib import Path
from typing import Any, Literal, Sequence

import import_exact_gram_bundle as gram

Q = Fraction
Matrix = tuple[tuple[Fraction, ...], ...]
Vector = tuple[Fraction, ...]
Status = Literal['psd', 'negative', 'asymmetric']
VERSION = 'v0.13D1'
INPUT_FORMAT = 'leanpep-rational-matrix-v1'
REPORT_FORMAT = 'leanpep-psd-synthesis-v1'


@dataclass(frozen=True)
class Factor:
    weight: Fraction
    vector: Vector


@dataclass(frozen=True)
class Result:
    status: Status
    dimension: int
    factors: tuple[Factor, ...] = ()
    pivots: tuple[int, ...] = ()
    witness: Vector | None = None
    quadratic_value: Fraction | None = None
    asymmetry: tuple[int, int] | None = None
    reason: str = ''


def exact_matrix(matrix: Sequence[Sequence[Fraction | int]]) -> Matrix:
    """Validate before arithmetic: notably bool and binary float are rejected."""
    if not isinstance(matrix, (list, tuple)):
        raise ValueError('matrix must be a list or tuple of rows')
    n = len(matrix)
    rows = []
    for i, row in enumerate(matrix):
        if not isinstance(row, (list, tuple)) or len(row) != n:
            raise ValueError(f'matrix[{i}]: expected {n} entries (square matrix)')
        if any(type(x) not in (int, Fraction) for x in row):
            raise ValueError(f'matrix[{i}]: use exact integers/Fractions, never floats or bools')
        rows.append(tuple(Q(x) for x in row))
    return tuple(rows)


def quadratic(matrix: Matrix, vector: Vector) -> Fraction:
    if len(vector) != len(matrix):
        raise ValueError('quadratic: vector dimension mismatch')
    return sum((vector[i] * matrix[i][j] * vector[j]
                for i in range(len(matrix)) for j in range(len(matrix))), Q(0))


def reconstruct(n: int, factors: Sequence[Factor]) -> Matrix:
    if any(len(t.vector) != n for t in factors):
        raise ValueError('factor dimension mismatch')
    return tuple(tuple(sum((t.weight * t.vector[i] * t.vector[j]
                            for t in factors), Q(0))
                       for j in range(n)) for i in range(n))


def verify_result(matrix: Sequence[Sequence[Fraction | int]], result: Result) -> bool:
    """Independent full-entry / witness check. Pivot/rank diagnostics are NOT trusted."""
    a = exact_matrix(matrix)
    n = len(a)
    if result.dimension != n:
        return False
    if result.status == 'psd':
        return (result.witness is None and result.asymmetry is None
                and all(type(t.weight) is Fraction and t.weight >= 0
                        and len(t.vector) == n
                        and all(type(x) is Fraction for x in t.vector)
                        for t in result.factors)
                and all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
                and reconstruct(n, result.factors) == a)
    if result.status == 'negative':
        v = result.witness
        return (v is not None and len(v) == n
                and all(type(x) is Fraction for x in v)
                and quadratic(a, v) == result.quadratic_value
                and quadratic(a, v) < 0)
    if result.status == 'asymmetric':
        ij = result.asymmetry
        return (ij is not None and len(ij) == 2
                and all(type(i) is int and 0 <= i < n for i in ij)
                and a[ij[0]][ij[1]] != a[ij[1]][ij[0]])
    return False


def synthesize_psd(matrix: Sequence[Sequence[Fraction | int]], *,
                   pivot_order: Sequence[int] | None = None) -> Result:
    """Exact pivoted Schur elimination in original coordinates, at most n pivots.

    After k positive pivots A = sum(d_j v_j v_j^T) + S. Previous pivot
    rows of S are zero, and v_j[p_j] = 1. A failure witness for S is lifted
    backwards to annihilate every earlier v_j. Positive output needs no
    square roots, including singular PSD matrices with irrational Cholesky.
    """
    a = exact_matrix(matrix)
    n = len(a)
    order = tuple(range(n)) if pivot_order is None else tuple(pivot_order)
    if len(order) != n or any(type(i) is not int for i in order) or set(order) != set(range(n)):
        raise ValueError('pivot_order must be a permutation of 0,...,n-1')
    for i in range(n):
        for j in range(i + 1, n):
            if a[i][j] != a[j][i]:
                return Result('asymmetric', n, asymmetry=(i, j), reason='exact asymmetry')
    s = [list(row) for row in a]
    active = list(order)
    factors: list[Factor] = []
    pivots: list[int] = []

    def negative(v: list[Fraction], reason: str) -> Result:
        # Solve v_j dot w = 0 in reverse pivot order. Do not return a Schur
        # coordinate vector as if it were an original-coordinate witness.
        for p, t in reversed(list(zip(pivots, factors))):
            v[p] = -sum((t.vector[j] * v[j] for j in range(n) if j != p), Q(0))
        w = tuple(v)
        result = Result('negative', n, tuple(factors), tuple(pivots),
                        w, quadratic(a, w), reason=reason)
        if not verify_result(a, result):
            raise ArithmeticError('internal error: negative witness failed exact recheck')
        return result

    while active:
        for i in active:
            if s[i][i] < 0:
                v = [Q(0)] * n
                v[i] = Q(1)
                return negative(v, 'negative Schur diagonal')
        for i in active:
            if s[i][i] == 0:
                for j in active:
                    if s[i][j] != 0:
                        v = [Q(0)] * n
                        v[j] = Q(1)
                        v[i] = -(s[j][j] + 1) / (2 * s[i][j])
                        return negative(v, 'zero Schur diagonal with nonzero row')
        p = next((i for i in active if s[i][i] > 0), None)
        if p is None:
            break  # All remaining rows are exactly zero, not merely small.
        d = s[p][p]
        v = tuple(s[i][p] / d if i in active else Q(0) for i in range(n))
        factors.append(Factor(d, v))
        pivots.append(p)
        for i in active:
            for j in active:
                s[i][j] -= d * v[i] * v[j]
        active.remove(p)
    result = Result('psd', n, tuple(factors), tuple(pivots), reason='exact factor identity')
    if not verify_result(a, result):
        raise ArithmeticError('internal error: PSD factors failed full-entry recheck')
    return result


def rat_json(q: Fraction) -> dict[str, int]:
    return {'num': q.numerator, 'den': q.denominator}


def matrix_json(a: Matrix) -> list[list[dict[str, int]]]:
    return [[rat_json(q) for q in row] for row in a]


def factor_json(t: Factor) -> dict[str, Any]:
    return {'weight': rat_json(t.weight), 'vector': [rat_json(x) for x in t.vector]}


def parse_matrix_input(raw: Any) -> Matrix:
    obj = gram.require_object(raw, '$')
    gram.check_keys(obj, '$', required=('format', 'dimension', 'matrix'))
    if obj['format'] != INPUT_FORMAT:
        raise ValueError(f'$.format: expected {INPUT_FORMAT}')
    n = gram.require_int(obj['dimension'], '$.dimension', minimum=0)
    return gram.parse_rational_matrix(obj['matrix'], '$.matrix', n, n)


def result_report(a: Matrix, result: Result) -> dict[str, Any]:
    report: dict[str, Any] = {
        'format': REPORT_FORMAT, 'producer_version': VERSION,
        'matrix_sha256': gram.canonical_json_sha256(matrix_json(a)),
        'dimension': len(a), 'status': result.status, 'reason': result.reason,
        'pivot_indices_original_basis': list(result.pivots),
        'python_exact_recheck': verify_result(a, result),
        'lean_status': 'not_run_by_this_producer',
        'scope': 'matrix only; not source audit, PEP feasibility, upper bound, or tightness',
    }
    if result.status == 'psd':
        report['factor_count'] = len(result.factors)
        report['factor_certificate'] = {'factors': [factor_json(t) for t in result.factors]}
    elif result.status == 'negative':
        report['witness_original_basis'] = [rat_json(x) for x in result.witness or ()]
        report['quadratic_value'] = rat_json(result.quadratic_value)  # type: ignore[arg-type]
    else:
        assert result.asymmetry is not None
        i, j = result.asymmetry
        report['asymmetry'] = {'i': i, 'j': j, 'left': rat_json(a[i][j]), 'right': rat_json(a[j][i])}
    return report


def render_matrix_lean(a: Matrix, result: Result, namespace: str) -> str:
    """Ordinary data and kernel proofs; the input matrix is not defined from factors."""
    parts = gram.validate_namespace(namespace)
    if not verify_result(a, result):
        raise ValueError('cannot render a result that fails independent exact recheck')
    n = len(a)
    target = gram.lean_matrix(a) if n else '(fun _ _ => 0)'
    lines = ['import LeanPEP.GramPEP.FactorReplacement', '',
             '/-! Generated by tools/synthesize_psd_factors.py. Untrusted candidate data.',
             'Every mathematical result below is checked by ordinary Lean proof terms.',
             'Matrix SHA-256: ' + gram.canonical_json_sha256(matrix_json(a)) + ' -/', '']
    lines += gram.render_namespace_open(parts)
    lines += ['', 'open LeanPEP.GramPEP', '', f'def matrixQ : Gram {n} ℚ := {target}', '']
    if result.status == 'psd':
        entries = [gram.RankOneFactorSpec(t.weight, t.vector) for t in result.factors]
        lines += [f'def factorQ : PSDFactorCertQ {n} :=', '  { factors :=']
        lines += gram.indent_lines(gram.render_record_list(entries, gram.render_factor), 4)
        lines += ['  }', '',
                  'theorem factor_check : checkPSDFactorQ matrixQ factorQ = true := by',
                  '  decide +kernel', '',
                  'theorem psd_rational : IsGramPosSemidef matrixQ :=',
                  '  checkPSDFactorQ_sound matrixQ factorQ factor_check', '',
                  'theorem psd_real : IsGramPosSemidef (castGramQ matrixQ) :=',
                  '  checkPSDFactorQ_sound_real matrixQ factorQ factor_check', '']
    elif result.status == 'negative':
        assert result.witness is not None
        lines += [f'def witnessQ : VecExpr {n} ℚ := {gram.lean_vector(result.witness)}', '',
                  'theorem negative_value : gramNormSq matrixQ witnessQ < 0 := by',
                  '  decide +kernel', '',
                  'theorem not_psd_rational : ¬ IsGramPosSemidef matrixQ :=',
                  '  not_isGramPosSemidef_of_negative matrixQ witnessQ negative_value', '',
                  'theorem not_psd_real : ¬ IsGramPosSemidef (castGramQ matrixQ) :=',
                  '  not_isGramPosSemidef_real_of_negative matrixQ witnessQ negative_value', '']
    else:
        assert result.asymmetry is not None
        i, j = result.asymmetry
        lines += [f'theorem asymmetric : matrixQ {i} {j} ≠ matrixQ {j} {i} := by',
                  '  decide +kernel', '',
                  'theorem not_psd_rational : ¬ IsGramPosSemidef matrixQ :=',
                  f'  not_isGramPosSemidef_of_asymmetry matrixQ {i} {j} asymmetric', '']
    lines += gram.render_namespace_close(parts)
    return '\n'.join(lines) + '\n'


def refactor_bundle(raw: Any, *, pivot_order: Sequence[int] | None = None
                    ) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Reuse external-gram-format-v1; replace ONLY factors and their two counts.

    Old factor values are shape-validated but are never used in synthesis.
    Matrix success deliberately does not assert full bundle acceptance.
    On failure no replacement bundle is returned, even if one matrix succeeds.
    """
    spec = gram.parse_bundle(raw)
    rp = synthesize_psd(spec.primal.gram, pivot_order=pivot_order)
    rd = synthesize_psd(spec.upper.dual_matrix, pivot_order=pivot_order)
    report: dict[str, Any] = {
        'format': 'leanpep-bundle-factor-synthesis-v1', 'producer_version': VERSION,
        'source_bundle_sha256': gram.canonical_json_sha256(raw),
        'primal': result_report(spec.primal.gram, rp),
        'dual': result_report(spec.upper.dual_matrix, rd),
        'full_bundle_acceptance': 'not_checked', 'source_formulation_audit': 'not_performed',
        'raw_reconstructed_policy': 'input exact matrices are not modified or reconstructed',
        'bundle_emitted': False,
    }
    if rp.status != 'psd' or rd.status != 'psd':
        return None, report
    out = copy.deepcopy(raw)
    out['primal']['gram_factor'] = {'factors': [factor_json(t) for t in rp.factors]}
    out['upper']['dual_factor'] = {'factors': [factor_json(t) for t in rd.factors]}
    out['declared']['primal_factor_count'] = len(rp.factors)
    out['declared']['dual_factor_count'] = len(rd.factors)
    gram.parse_bundle(out)
    report.update(bundle_emitted=True, replacement_bundle_sha256=gram.canonical_json_sha256(out),
                  allowed_changes=['primal.gram_factor', 'upper.dual_factor',
                                   'declared.primal_factor_count', 'declared.dual_factor_count'])
    return out, report


def render_bundle_data(raw: dict[str, Any], namespace: str) -> str:
    # The old importer is reused unchanged. Suppress its historical native_decide
    # expectation branch; matrix-only synthesis never asserts full PEP acceptance.
    spec = replace(gram.parse_bundle(raw), expect='unchecked')
    return gram.render_module(spec, namespace)


def dumps(raw: Any) -> str:
    return json.dumps(raw, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    for mode in ('matrix', 'bundle'):
        p = sub.add_parser(mode)
        p.add_argument('input', type=Path)
        p.add_argument('--output', required=True, type=Path,
                       help='matrix result report, or replacement exact bundle')
        p.add_argument('--lean', type=Path)
        p.add_argument('--namespace', default='LeanPEP.Imported.SynthesizedPSD')
        p.add_argument('--pivot-order', help='comma-separated permutation, in original coordinates')
        if mode == 'bundle':
            p.add_argument('--report', required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        paths = [args.input.resolve(), args.output.resolve()]
        if args.lean is not None:
            paths.append(args.lean.resolve())
            gram.validate_namespace(args.namespace)
        if args.mode == 'bundle':
            paths.append(args.report.resolve())
        if len(set(paths)) != len(paths):
            raise ValueError('input/output/report/Lean paths must be distinct')
        order = None if args.pivot_order is None else tuple(int(s) for s in args.pivot_order.split(',') if s)
        raw = gram.load_json(args.input)
        if args.mode == 'matrix':
            a = parse_matrix_input(raw)
            result = synthesize_psd(a, pivot_order=order)
            report = result_report(a, result)
            lean = render_matrix_lean(a, result, args.namespace) if args.lean is not None else None
            gram.atomic_write(args.output, dumps(report))
            if lean is not None:
                gram.atomic_write(args.lean, lean)
            print(f'{result.status}: exact matrix diagnostic; Lean acceptance not executed')
            return 0 if result.status == 'psd' else 1
        out, report = refactor_bundle(raw, pivot_order=order)
        lean = render_bundle_data(out, args.namespace) if out is not None and args.lean is not None else None
        gram.atomic_write(args.report, dumps(report))
        if out is None:
            print('matrix failure: no bundle/Lean file written; pre-existing outputs are untouched', file=sys.stderr)
            return 1
        gram.atomic_write(args.output, dumps(out))
        if lean is not None:
            gram.atomic_write(args.lean, lean)
        print('both matrices factored exactly; full bundle and source audit NOT checked')
        return 0
    except (ValueError, gram.ImportFormatError, OSError, ArithmeticError) as exc:
        print(f'synthesis error: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
