#!/usr/bin/env python3
"""D5: exact signed row conventions and positive scaling before D4 ordering.

Raw inequalities are q >= 0 or q <= 0. Upper multipliers are explicitly
NONNEGATIVE multipliers on the oriented rows (q or -q), not raw solver-signed
multipliers. Normalization maps q to orient(q)/alpha and lambda to lambda*alpha.
No guessed scale, sign correction, deleted row, rounded coefficient, or solver
call is permitted. Generated Lean contains submitted data, not acceptance proofs.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
from typing import Any

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_coordinates as native
import import_proximal_gradient_ordering as order

FORMAT = 'leanpep-scaled-pg-source-v1'
CONVENTION = 'nonnegative_on_oriented_rows_v1'
AS = 'LeanPEP.Adapters.ProximalGradientRows'


@dataclass(frozen=True)
class Rule:
    sense: str
    scale: Q


@dataclass(frozen=True)
class Artifact:
    ordered: order.Artifact
    rules: tuple[Rule, ...]
    sha256: str


def orient(r: Rule, e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    if r.sense not in ('geZero', 'leZero'):
        raise ValueError('unknown row sense')
    return e if r.sense == 'geZero' else centered.scale(Q(-1), e)


def inv(a: Q) -> Q:
    """Match Lean field inversion at zero; the independent strict-positive guard rejects it."""
    return Q(0) if a == 0 else 1/a


def normalize(r: Rule, e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return centered.scale(inv(r.scale), orient(r, e))


def encode(r: Rule, e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return orient(r, centered.scale(r.scale, e))


def artifact_tree(a: Artifact) -> dict[str, Any]:
    d = order.artifact_tree(a.ordered)
    d['format'] = FORMAT
    d['multiplier_convention'] = CONVENTION
    d['row_rules'] = centered.exact_json([dict(sense=r.sense, scale=r.scale) for r in a.rules])
    return d


def parse_artifact(raw: Any, expected_steps: int | None = None) -> Artifact:
    d = gram.require_object(raw, '$')
    gram.check_keys(d, '$', required=('format', 'horizon', 'origin', 'source', 'upper',
        'ordering', 'row_rules', 'multiplier_convention'))
    if d['format'] != FORMAT:
        gram.fail('$.format', 'unsupported row format')
    if d['multiplier_convention'] != CONVENTION:
        gram.fail('$.multiplier_convention', 'only nonnegative weights on oriented rows are supported')
    lower = {k:v for k,v in d.items() if k not in ('row_rules', 'multiplier_convention')}
    lower['format'] = order.FORMAT
    a = order.parse_artifact(lower, expected_steps)
    xs = gram.require_array(d['row_rules'], '$.row_rules')
    k = len(a.payload.source.constraints)
    if len(xs) != k:
        gram.fail('$.row_rules', f'exactly {k} source-order rules required, got {len(xs)}')
    rs = []
    for i, raw_r in enumerate(xs):
        path = f'$.row_rules[{i}]'
        r = gram.require_object(raw_r, path)
        gram.check_keys(r, path, required=('sense', 'scale'))
        if r['sense'] not in ('geZero', 'leZero'):
            gram.fail(path+'.sense', 'must be geZero or leZero; equality/strict inequality not supported')
        # Zero/negative rational scales remain representable for independent Lean rejection.
        rs.append(Rule(r['sense'], gram.parse_rational(r['scale'], path+'.scale')))
    return Artifact(a, tuple(rs), gram.canonical_json_sha256(d))


def oriented_artifact(a: Artifact) -> native.Artifact:
    b = a.ordered.payload
    if len(a.rules) != len(b.source.constraints):
        raise ValueError('row-rule count mismatch')
    s = replace(b.source, constraints=tuple(orient(r,e) for r,e in zip(a.rules,b.source.constraints)))
    return replace(b, source=s)


def normalized_artifact(a: Artifact) -> order.Artifact:
    b = a.ordered.payload
    if len(a.rules) != len(b.source.constraints):
        raise ValueError('row-rule count mismatch')
    s = replace(b.source, constraints=tuple(normalize(r,e) for r,e in zip(a.rules,b.source.constraints)))
    # Row index is STILL in source storage order here; D4 handles its later inverse permutation.
    c = replace(b.upper, assumption_terms=tuple(replace(t, weight=t.weight*a.rules[t.index].scale)
        for t in b.upper.assumption_terms))
    result = replace(a.ordered, payload=replace(b, source=s, upper=c))
    return replace(result, sha256=gram.canonical_json_sha256(order.artifact_tree(result)))


def assumption_sum(a: native.Artifact) -> gram.LinearExprSpec:
    s, c = a.source, a.upper
    out = centered.zero(len(s.objective.value_coeff), len(s.objective.gram_coeff))
    for t in c.assumption_terms:
        out = centered.add(out, centered.scale(t.weight, s.constraints[t.index]))
    return out


def diagnose(a: Artifact) -> dict[str, Any]:
    raw = oriented_artifact(a)
    normalized = normalized_artifact(a)
    lower = order.diagnose(normalized)
    local = native.local_check(raw.source, raw.upper)
    positive = [r.scale > 0 for r in a.rules]
    restored = tuple(encode(r,e) for r,e in zip(a.rules, normalized.payload.source.constraints))
    guards = dict(positive_scales=all(positive),
        normalized_source=all(lower['permutation_guards'].values()) and lower['bound_guards']['canonical_source'],
        oriented_source_certificate=local['accepted'],
        empty_implicit_interpolation=not raw.upper.interp_terms,
        source_objective=raw.upper.objective==raw.source.objective,
        normalized_bound=lower['diagnostic_passed'])
    return dict(format='leanpep-scaled-pg-diagnostic-v1', horizon=raw.horizon,
        canonical_json_sha256=a.sha256, origin=raw.origin,
        multiplier_convention=CONVENTION,
        positive_scale_guards=positive, bound_guards=guards,
        oriented_source_certificate=local, normalized_diagnostic=lower,
        row_roundtrip=restored==a.ordered.payload.source.constraints,
        weighted_assumption_sum_preserved=assumption_sum(raw)==assumption_sum(normalized.payload),
        diagnostic_passed=all(guards.values()),
        lean_checked=False, live_capture_performed=False, provenance_authenticated=False,
        numeric_interpretation='exact_num_den_no_reconstruction',
        multiplier_transport='source_lambda_times_source_row_positive_scale_then_D4_row_inverse',
        arbitrary_row_deletion_supported=False, equality_rows_supported=False,
        raw_solver_signed_multipliers_supported=False, primal_import_supported=False)


def render_module(a: Artifact, namespace: str) -> str:
    gram.validate_namespace(namespace)
    # Reuse the old, unchanged DATA renderer. Its snapshot remains RAW here.
    text = order.render_module(a.ordered, namespace)
    text = text.replace(f'import {order.AS}', f'import {AS}', 1)
    text = text.replace('D4 generated exact permuted data.', 'D5 generated exact signed/scaled raw data.')
    text = text.replace(f'open LeanPEP.GramPEP {order.AS}',
        f'open LeanPEP.GramPEP {AS}\nopen {order.AS} (OrderingQ SnapshotQ)')
    text = text.replace(gram.lean_string(a.ordered.sha256), gram.lean_string(a.sha256), 1)
    n = a.ordered.payload.horizon-1
    rules = '!['+', '.join('{ sense := .'+r.sense+', scale := '+gram.lean_rat(r.scale)+' }'
        for r in a.rules)+']'
    marker = f'def sourceQ : SourceQ {n} :='
    text = text.replace(marker, f'def rulesQ : Fin ({order.AS}.rowCount {n}) → '
        f'LeanPEP.GramPEP.RowNormalization.RuleQ :=\n  {rules}\n\n'+marker, 1)
    text = text.replace('{ ordering := orderingQ, snapshot := snapshotQ }',
        '{ ordering := orderingQ, snapshot := snapshotQ, rules := rulesQ }', 1)
    return text


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    ap.add_argument('--namespace', required=True)
    ap.add_argument('--expected-steps', type=int)
    ap.add_argument('--normalized-json', type=Path)
    ap.add_argument('--require-diagnostic-pass', action='store_true')
    args = ap.parse_args(argv)
    paths = [args.input,args.lean,args.report]+([args.normalized_json] if args.normalized_json else [])
    if len({p.resolve() for p in paths}) != len(paths):
        ap.error('all input/output paths must be distinct')
    try:
        a = parse_artifact(gram.load_json(args.input), args.expected_steps)
        text, report = render_module(a,args.namespace), diagnose(a)
        gram.atomic_write(args.lean, text)
        gram.atomic_write(args.report, json.dumps(report,indent=2,sort_keys=True)+'\n')
        if args.normalized_json:
            gram.atomic_write(args.normalized_json, json.dumps(
                order.artifact_tree(normalized_artifact(a)),indent=2,sort_keys=True)+'\n')
        print('Python diagnostics:',report['diagnostic_passed'],'; Lean has NOT been run.')
        return 2 if args.require_diagnostic_pass and not report['diagnostic_passed'] else 0
    except (ValueError,OSError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
