#!/usr/bin/env python3
"""D12: bind an emitted D10/D11 system to the Lean-defined certificate family.

No new solver and no numerical repair. The old completion outputs are preserved.
A separate exact diagnostic compares ALL equations/endpoints and a new Lean
replay checks the binding before transporting positive/negative conclusions.
Python diagnostics do not certify the replay. This is not live solver capture.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
from typing import Any

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_sparse as sparse
import import_pepit_proximal_gradient_capture as cap
import prepare_proximal_gradient_candidates as prep
import complete_pepit_proximal_gradient_capture as linear
import complete_bounded_pepit_capture as bounded
import solve_exact_linear_system as ls

UC = 'LeanPEP.GramPEP.UpperCoefficientSystem'
UB = 'LeanPEP.GramPEP.UpperCoefficientBox'


def coefficient_tags(p: int, m: int) -> tuple[tuple[str, int, int], ...]:
    if type(p) is not int or type(m) is not int or p < 0 or m < 0:
        raise ValueError('coefficient dimensions must be nonnegative integers')
    return (('constant', 0, 0),) + tuple(('value', i, 0) for i in range(p)) + tuple(
        ('gram', i, j) for i in range(m) for j in range(m))


def coefficient(e: gram.LinearExprSpec, tag: tuple[str, int, int]) -> Q:
    kind, i, j = tag
    if kind == 'constant': return e.const
    if kind == 'value': return e.value_coeff[i]
    if kind == 'gram': return e.gram_coeff[i][j]
    raise ValueError('unknown coefficient tag')


def family_system(a: sparse.Artifact) -> ls.System:
    """Independent diagnostic implementation of D12's Lean compiler.

    It reads the original model and reference list, NOT a generated matrix. A
    separate Lean check binds the untrusted matrix to compileQ (ofUpperQ seed).
    """
    u = a.upper
    if u.interp_terms:
        raise ValueError('implicit interpolation is unsupported, not silently erased')
    p, m = len(u.objective.value_coeff), len(u.dual_matrix)
    if len(u.objective.gram_coeff) != m or any(len(row) != m for row in u.dual_matrix):
        raise ValueError('invalid fixed matrix dimensions')
    rows = sparse.compact_snapshot(a).constraints
    for t in u.assumption_terms:
        if not 0 <= t.index < len(rows): raise ValueError('out-of-range reference')
    A, rhs = [], []
    for tag in coefficient_tags(p, m):
        A.append((Q(tag[0] == 'constant'),) + tuple(
            -coefficient(rows[t.index], tag) for t in u.assumption_terms))
        rhs.append(coefficient(u.objective, tag) +
            (u.dual_matrix[tag[1]][tag[2]] if tag[0] == 'gram' else Q(0)))
    return ls.System.make(1 + len(u.assumption_terms), A, rhs)


def system_binding(a: sparse.Artifact, submitted: ls.System) -> dict[str, Any]:
    expected = family_system(a)
    size_ok = submitted.columns == expected.columns and len(submitted.rhs) == len(expected.rhs)
    differences: list[dict[str, Any]] = []
    tags = coefficient_tags(len(a.upper.objective.value_coeff), len(a.upper.dual_matrix))
    if size_ok:
        for i, tag in enumerate(tags):
            if submitted.rhs[i] != expected.rhs[i]:
                differences.append(dict(row=i, coefficient=tag, column='rhs'))
            for j in range(expected.columns):
                if submitted.matrix[i][j] != expected.matrix[i][j]:
                    differences.append(dict(row=i, coefficient=tag, column=j))
    return dict(dimensions_match=size_ok, matrix_and_rhs_match=size_ok and not differences,
        row_order='constant, values, all ordered Gram entries (row major)',
        column_order='bound, original multiplier occurrences (not unique references)',
        expected_rows=len(expected.rhs), expected_columns=expected.columns,
        mismatches=differences)


def vector_binding(seed: gram.UpperSpec, raw: gram.UpperSpec, vector: tuple[Q, ...]) -> bool:
    return ([t.index for t in seed.assumption_terms] == [t.index for t in raw.assumption_terms]
            and vector == (raw.bound,) + tuple(t.weight for t in raw.assumption_terms))


def endpoint_binding(raw: tuple[Q, ...], eta: Q, lower: tuple[Q, ...], upper: tuple[Q, ...]) -> bool:
    if len(lower) != len(raw) or len(upper) != len(raw): return False
    return all(lower[j] == (raw[j] - eta if j == 0 else max(Q(0), raw[j] - eta)) and
               upper[j] == raw[j] + eta for j in range(len(raw)))


@dataclass(frozen=True)
class Audit:
    mode: str
    result: Any
    report: dict[str, Any]
    raw_vector: tuple[Q, ...]


def run(data: Any, mode: str, expected_steps: int | None = None, *, max_pivots: int = 10000) -> Audit:
    if mode not in ('linear', 'box'): raise ValueError('mode must be linear or box')
    result = (linear.complete(data, expected_steps) if mode == 'linear' else
              bounded.complete(data, expected_steps, max_pivots=max_pivots))
    prev = result if mode == 'linear' else result.previous
    prepared = prev.capture.prepared
    if prepared is None: raise ValueError('prepared-only capture has no numerical family')
    seed, raw = prepared.reconstructed.artifact, prepared.raw.artifact.upper
    v = (raw.bound,) + tuple(t.weight for t in raw.assumption_terms)
    binding = system_binding(seed, prev.system)
    endpoints = True if mode == 'linear' else endpoint_binding(
        v, prepared.policy.max_abs_error, result.box.lower, result.box.upper)
    source = cap.trace_diagnostic(prev.capture)
    raw_binding = cap.raw_binding_diagnostic(prev.capture, raw)
    policy = prep.changes_diagnostic(prepared.policy, raw, seed.upper)
    valid = (binding['matrix_and_rhs_match'] and endpoints and vector_binding(seed.upper, raw, v)
             and all(source.values()) and all(raw_binding.values()) and all(policy.values()))
    status = prev.linear.status if mode == 'linear' else result.result.status
    return Audit(mode, result, dict(format='leanpep-compiled-system-binding-v1', mode=mode,
        lean_checked=False, live_capture_performed=False, producer_authenticated=False,
        solver_replaced=False, residual_recomputed=False, source_coefficients_changed=False,
        source_checks=source, trace_raw_binding=raw_binding, seed_policy_checks=policy,
        system_binding=binding, raw_vector_binding=vector_binding(seed.upper, raw, v),
        box_endpoint_binding=endpoints, binding_diagnostic_passed=bool(valid),
        previous_status=status, previous_completion_accepted=result.report['completion_accepted'],
        negative_scope='Only this fixed objective/residual/reference family; in box mode also this raw budget. '
          'Not general PEP infeasibility, another residual, or completeness of denominator search.',
        python_compiler_verified=False, lean_defined_compiler_and_instance_binding=True), v)


def render_binding_replay(a: Audit, namespace: str) -> str:
    gram.validate_namespace(namespace)
    render = linear.render_replay if a.mode == 'linear' else bounded.render_replay
    text = render(a.result, namespace)
    if not a.report['binding_diagnostic_passed']:
        # The old replay may itself fail on malformed sources. Do not attach a
        # new positive binding or a transported negative claim to such input.
        return text + '\n-- D12 binding diagnostic failed: no transported D12 conclusion.\n'
    prev = a.result if a.mode == 'linear' else a.result.previous
    q = prev.system.columns
    text += f'''\nnamespace {namespace}
open LeanPEP.GramPEP

def auditedFamilyQ := {UC}.ofUpperQ reconstructedUpperQ
def auditRawVectorQ : Fin {q} → ℚ := {gram.lean_vector(a.raw_vector)}

theorem audited_trace_check : {cap.AS}.checkTraceQ sourceQ traceQ = true := by
  decide +kernel
theorem audited_trace_raw_check : {cap.AS}.checkRawBindingQ sourceQ traceQ rawUpperQ = true := by
  decide +kernel
theorem audited_seed_empty : reconstructedUpperQ.interpTerms = [] := by
  decide +kernel
theorem audited_seed_policy : RationalReconstructionAudit.checkChangesQ policyQ rawUpperQ reconstructedUpperQ = true := by
  decide +kernel
theorem audited_raw_vector : {UB}.checkRawVectorQ reconstructedUpperQ rawUpperQ auditRawVectorQ = true := by
  decide +kernel
theorem compiler_binding : {UC}.checkSystemQ auditedFamilyQ coefficientSystemQ = true := by
  decide +kernel
'''
    if a.mode == 'box':
        text += f'''theorem compiler_box_binding : {UB}.checkBoxQ auditedFamilyQ auditRawVectorQ policyQ.maxAbsError boxQ = true := by
  decide +kernel
'''
        if a.result.result.obstruction is not None:
            text += f'''theorem no_fixed_family_in_budget : ¬ ∃ x,
    checkUpperCertQ ({UC}.instantiateQ auditedFamilyQ x) = true ∧
      {UB}.WithinBudgetQ auditRawVectorQ x policyQ.maxAbsError :=
  {UB}.checked_no_accepted_in_budget auditedFamilyQ auditRawVectorQ policyQ.maxAbsError
    boxQ compiler_box_binding boxObstructionQ (by decide +kernel)
#print axioms no_fixed_family_in_budget
'''
    elif a.result.linear.obstruction is not None:
        text += f'''theorem no_fixed_family_certificate : ¬ ∃ x,
    checkUpperCertQ ({UC}.instantiateQ auditedFamilyQ x) = true :=
  {UC}.checked_no_accepted auditedFamilyQ coefficientSystemQ compiler_binding
    obstructionQ (by decide +kernel)
#print axioms no_fixed_family_certificate
'''
    if a.result.report['completion_accepted']:
        text += f'''theorem compiled_family_accepted : checkUpperCertQ
    ({UC}.instantiateQ auditedFamilyQ completionVectorQ) = true := by
  decide +kernel
#print axioms compiled_family_accepted
'''
    return text + f'#print axioms compiler_binding\nend {namespace}\n'


def outputs(a: Audit, directory: Path, namespace: str) -> dict[Path, str]:
    out = (linear.outputs if a.mode == 'linear' else bounded.outputs)(a.result, directory, namespace)
    out[directory / 'compiler_binding_report.json'] = json.dumps(a.report, indent=2, sort_keys=True) + '\n'
    out[directory / 'BindingReplay.lean'] = render_binding_replay(a, namespace)
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('--mode', choices=('linear', 'box'), default='box')
    ap.add_argument('--expected-steps', type=int)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--namespace', required=True)
    ap.add_argument('--max-pivots', type=int, default=10000)
    args = ap.parse_args(argv)
    try:
        a = run(gram.load_json(args.input), args.mode, args.expected_steps, max_pivots=args.max_pivots)
        out = outputs(a, args.output_dir, args.namespace)
        if any(p.resolve() == args.input.resolve() for p in out): raise ValueError('output would overwrite capture')
        if args.output_dir.exists() and any(args.output_dir.iterdir()):
            raise ValueError('output directory must be empty; refusing stale artifacts')
        for p, t in out.items(): gram.atomic_write(p, t)
        print(json.dumps(a.report, sort_keys=True))
        return 0 if a.report['binding_diagnostic_passed'] else 2
    except (ValueError, ArithmeticError, OSError) as exc:
        print('error: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__': raise SystemExit(main())
