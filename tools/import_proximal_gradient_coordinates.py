#!/usr/bin/env python3
"""D3 exact uncentered PG snapshots: check rectangular maps and origin round trips.

No floats, solver, reordering, reconstruction or live provenance. The supported
leaf order is explicit, not automatically inferred from PEPit. Code generation
submits native data; Lean computes the restriction and checks BOTH certificates.
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
import synthesize_psd_factors as psd

FORMAT = 'leanpep-uncentered-pg-source-v1'
COORDINATES = 'uncentered-xstar-x0-gstar-gradients-residuals-v1'
AS = 'LeanPEP.Adapters.ProximalGradientCoordinates'
Matrix = tuple[tuple[Q, ...], ...]


@dataclass(frozen=True)
class Artifact:
    horizon: int
    origin: dict[str, str]
    source: centered.Snapshot
    center_matrix: Matrix
    section_matrix: Matrix
    upper: gram.UpperSpec
    sha256: str


def dimensions(T: int) -> tuple[int, int, int]:
    p, m = centered.dimensions(T)
    return p, m, m+1


def maps(m: int) -> tuple[Matrix, Matrix]:
    """Z=C Y, Y0=J Z, C J=I; J C is NOT I on native coordinates."""
    if type(m) is not int or m < 1:
        raise ValueError('centered dimension must be a positive integer')
    C = tuple((Q(-int(i == 0)),)+centered.unit(m, i) for i in range(m))
    J = ((Q(0),)*m,)+tuple(centered.unit(m, i) for i in range(m))
    return C, J


def restrict_matrix(S: Matrix) -> Matrix:
    return tuple(row[1:] for row in S[1:])


def lift_matrix(S: Matrix) -> Matrix:
    """C^T S C; both off-diagonal blocks are retained, even if S is asymmetric."""
    return ((S[0][0],)+tuple(-t for t in S[0]),)+tuple((-row[0],)+row for row in S)


def restrict_expr(e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return replace(e, gram_coeff=restrict_matrix(e.gram_coeff))


def lift_expr(e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return replace(e, gram_coeff=lift_matrix(e.gram_coeff))


def restrict_sample(s: centered.Sample) -> centered.Sample:
    return centered.Sample(s.value_index, s.position[1:], s.oracle[1:])


def lift_sample(s: centered.Sample) -> centered.Sample:
    return centered.Sample(s.value_index, (Q(1)-s.position[0],)+s.position,
                           (-s.oracle[0],)+s.oracle)


def expected_header(T: int) -> dict[str, Any]:
    h = centered.expected_snapshot(T).header.copy()
    h.update(coordinates=COORDINATES, basis_count=h['basis_count']+1,
             basis_order=('x_star', 'x0')+h['basis_order'][1:])
    return h


def restrict_snapshot(a: Artifact) -> centered.Snapshot:
    s = a.source
    h = s.header.copy()
    eh = centered.expected_snapshot(a.horizon).header
    # Only coordinate fields are converted; the complete NATIVE header is audited too.
    for key in ('coordinates', 'basis_count', 'basis_order'):
        h[key] = eh[key]
    return centered.Snapshot(h, tuple(map(restrict_sample, s.smooth_samples)),
        tuple(map(restrict_sample, s.nonsmooth_samples)),
        tuple(map(restrict_expr, s.constraints)), restrict_expr(s.objective))


def restrict_upper(c: gram.UpperSpec) -> gram.UpperSpec:
    return replace(c, objective=restrict_expr(c.objective), dual_matrix=restrict_matrix(c.dual_matrix),
        dual_factor=gram.FactorCertSpec(tuple(gram.RankOneFactorSpec(t.weight, t.vector[1:])
                                             for t in c.dual_factor.factors)))


def upper_tree(c: gram.UpperSpec) -> dict[str, Any]:
    return dict(bound=c.bound, objective=expr_tree(c.objective),
        interp_terms=[dict(weight=t.weight, i=t.i, j=t.j) for t in c.interp_terms],
        assumption_terms=[dict(weight=t.weight, index=t.index) for t in c.assumption_terms],
        dual_matrix=c.dual_matrix,
        dual_factor=dict(factors=[dict(weight=t.weight, vector=t.vector) for t in c.dual_factor.factors]))


def expr_tree(e: gram.LinearExprSpec) -> dict[str, Any]:
    return dict(const=e.const, value_coeff=e.value_coeff, gram_coeff=e.gram_coeff)


def centered_artifact(a: Artifact) -> centered.Artifact:
    s, c = restrict_snapshot(a), restrict_upper(a.upper)
    raw = centered.exact_json(dict(format=centered.FORMAT, horizon=a.horizon,
        origin=a.origin, source=centered.source_tree(s), upper=upper_tree(c)))
    return centered.parse_artifact(raw, a.horizon)


def centered_json(a: Artifact) -> dict[str, Any]:
    return centered.exact_json(dict(format=centered.FORMAT, horizon=a.horizon, origin=a.origin,
        source=centered.source_tree(restrict_snapshot(a)), upper=upper_tree(restrict_upper(a.upper))))


def parse_artifact(raw: Any, expected_steps: int | None = None) -> Artifact:
    d = gram.require_object(raw, '$')
    gram.check_keys(d, '$', required=('format', 'horizon', 'origin', 'source', 'upper'))
    if d['format'] != FORMAT:
        gram.fail('$.format', 'unsupported uncentered profile format')
    T = gram.require_int(d['horizon'], '$.horizon', minimum=1)
    if expected_steps is not None and T != expected_steps:
        gram.fail('$.horizon', f'expected caller-selected horizon {expected_steps}')
    p, m, q = dimensions(T)
    origin = gram.require_object(d['origin'], '$.origin')
    gram.check_keys(origin, '$.origin', required=('mode', 'description'))
    origin = dict(mode=centered._enum(origin['mode'], '$.origin.mode',
        ('deterministic_regression_fixture', 'external_exact_snapshot')),
        description=gram.require_string(origin['description'], '$.origin.description'))
    s = gram.require_object(d['source'], '$.source')
    gram.check_keys(s, '$.source', required=('header', 'center_matrix', 'section_matrix',
        'smooth_samples', 'nonsmooth_samples', 'constraints', 'objective'))
    def samples(key: str) -> tuple[centered.Sample, ...]:
        out = []
        for k, raw_sample in enumerate(gram.require_array(s[key], '$.source.'+key)):
            loc = f'$.source.{key}[{k}]'
            t = gram.require_object(raw_sample, loc)
            gram.check_keys(t, loc, required=('value_index', 'position', 'oracle'))
            i = gram.require_int(t['value_index'], loc+'.value_index', minimum=0)
            if i >= p:
                gram.fail(loc+'.value_index', 'out of range')
            out.append(centered.Sample(i, gram.parse_rational_vector(t['position'], loc+'.position', q),
                gram.parse_rational_vector(t['oracle'], loc+'.oracle', q)))
        return tuple(out)
    snapshot = centered.Snapshot(centered.parse_header(s['header']), samples('smooth_samples'),
        samples('nonsmooth_samples'),
        tuple(gram.parse_linear_expr(e, f'$.source.constraints[{k}]', p, q)
              for k, e in enumerate(gram.require_array(s['constraints'], '$.source.constraints'))),
        gram.parse_linear_expr(s['objective'], '$.source.objective', p, q))
    C = gram.parse_rational_matrix(s['center_matrix'], '$.source.center_matrix', m, q)
    J = gram.parse_rational_matrix(s['section_matrix'], '$.source.section_matrix', q, m)
    c = gram.parse_upper(d['upper'], '$.upper', p, q, len(snapshot.constraints))
    return Artifact(T, origin, snapshot, C, J, c, gram.canonical_json_sha256(d))


def local_check(s: centered.Snapshot, c: gram.UpperSpec) -> dict[str, bool]:
    """Independent exact arithmetic mirror of the OLD explicit carrier checker."""
    p, q = len(c.objective.value_coeff), len(c.dual_matrix)
    rhs = centered.zero(p, q)
    for t in c.assumption_terms:
        rhs = centered.add(rhs, centered.scale(t.weight, s.constraints[t.index]))
    for t in c.interp_terms:
        e = centered.add(centered.value(p,q,t.i), centered.scale(Q(-1), centered.value(p,q,t.j)))
        rhs = centered.add(rhs, centered.scale(t.weight, e))
    rhs = centered.add(rhs, gram.LinearExprSpec(Q(0), (Q(0),)*p, c.dual_matrix))
    target = centered.add(replace(centered.zero(p,q), const=c.bound), centered.scale(Q(-1), c.objective))
    fs = tuple(psd.Factor(t.weight, t.vector) for t in c.dual_factor.factors)
    factor_ok = all(t.weight >= 0 for t in fs) and psd.reconstruct(q, fs) == c.dual_matrix
    sym = all(c.dual_matrix[i][j] == c.dual_matrix[j][i] for i in range(q) for j in range(q))
    weights = all(t.weight >= 0 for t in c.assumption_terms+c.interp_terms)
    return dict(identity=rhs == target, factor=factor_ok, symmetric=sym, weights=weights,
                accepted=(rhs == target and factor_ok and sym and weights))


def diagnose(a: Artifact) -> dict[str, Any]:
    p,m,q = dimensions(a.horizon)
    t = restrict_snapshot(a)
    C,J = maps(m)
    actual = centered.source_tree(a.source)
    reconstructed = dict(header=expected_header(a.horizon),
        smooth_samples=centered.source_tree(replace(t, smooth_samples=tuple(map(lift_sample,t.smooth_samples))))['smooth_samples'],
        nonsmooth_samples=centered.source_tree(replace(t,nonsmooth_samples=tuple(map(lift_sample,t.nonsmooth_samples))))['nonsmooth_samples'],
        constraints=tuple(expr_tree(lift_expr(e)) for e in t.constraints),
        objective=expr_tree(lift_expr(t.objective)))
    mismatch = centered.differences(reconstructed, actual, '$.source')
    mismatch += centered.differences(C,a.center_matrix,'$.source.center_matrix')
    mismatch += centered.differences(J,a.section_matrix,'$.source.section_matrix')
    cd = centered.diagnose(centered_artifact(a))
    native = local_check(a.source,a.upper)
    guards = dict(header=actual['header']==reconstructed['header'],
        center_matrix=a.center_matrix==C, section_matrix=a.section_matrix==J,
        smooth_roundtrip=actual['smooth_samples']==reconstructed['smooth_samples'],
        nonsmooth_roundtrip=actual['nonsmooth_samples']==reconstructed['nonsmooth_samples'],
        constraints_roundtrip=actual['constraints']==reconstructed['constraints'],
        objective_roundtrip=actual['objective']==reconstructed['objective'],
        centered_source=cd['guards']['source'])
    source_ok = all(guards.values())
    bound_guards = dict(source=source_ok, native_certificate=native['accepted'],
        empty_implicit_interpolation=not a.upper.interp_terms,
        native_objective=a.upper.objective==a.source.objective,
        centered_bound=cd['diagnostic_passed'])
    return dict(format='leanpep-uncentered-pg-diagnostic-v1', horizon=a.horizon,
        canonical_json_sha256=a.sha256, origin=a.origin, dimensions=dict(values=p,centered=m,native=q),
        source_guards=guards, source_mismatches=mismatch,
        centered_source_mismatches=cd['source_mismatches'], native_certificate=native,
        centered_certificate=cd['guards'], bound_guards=bound_guards,
        diagnostic_passed=all(bound_guards.values()),
        lean_checked=False, live_capture_performed=False, provenance_authenticated=False,
        coordinate_contract='fixed_rectangular_center_map_and_zero_origin_section_with_full_roundtrip',
        arbitrary_pepit_order_supported=False, primal_transport_checked=False,
        numeric_interpretation='exact_num_den_no_reconstruction')


def render_module(a: Artifact, namespace: str) -> str:
    """Reuse D2's literal record renderer. Never replace submitted arrays by expected ones."""
    tmp = centered.Artifact(a.horizon,a.origin,a.source,a.upper,a.sha256)
    text = centered.render_module(tmp, namespace)
    text = text.replace(f'import {centered.AS}\n', f'import {AS}\n', 1)
    text = text.replace(f'open LeanPEP.GramPEP {centered.AS}\n', f'open LeanPEP.GramPEP {AS}\n', 1)
    text = text.replace('D2 generated exact centered snapshot.', 'D3 generated exact uncentered snapshot.', 1)
    marker = '\n    smoothSamples :='
    matrices = '\n    centerMatrix := '+gram.lean_matrix(a.center_matrix)+'\n'
    matrices += '    sectionMatrix := '+gram.lean_matrix(a.section_matrix)+'\n'
    if text.count(marker)!=1:
        raise ValueError('upstream renderer layout mismatch')
    return text.replace(marker,matrices+marker,1)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--report',type=Path,required=True)
    ap.add_argument('--namespace',required=True)
    ap.add_argument('--expected-steps',type=int)
    ap.add_argument('--centered-json',type=Path)
    ap.add_argument('--require-diagnostic-pass',action='store_true')
    args = ap.parse_args(argv)
    paths=[args.input,args.lean,args.report]+([args.centered_json] if args.centered_json else [])
    if len({p.resolve() for p in paths})!=len(paths):
        ap.error('all input/output paths must be distinct')
    try:
        a=parse_artifact(gram.load_json(args.input),args.expected_steps)
        text=render_module(a,args.namespace)
        report=diagnose(a)
        gram.atomic_write(args.lean,text)
        gram.atomic_write(args.report,json.dumps(report,indent=2,sort_keys=True)+'\n')
        if args.centered_json:
            gram.atomic_write(args.centered_json,json.dumps(centered_json(a),indent=2,sort_keys=True)+'\n')
        print('Python diagnostics:',report['diagnostic_passed'],'; Lean has NOT been run.')
        return 2 if args.require_diagnostic_pass and not report['diagnostic_passed'] else 0
    except (ValueError,OSError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2


if __name__=='__main__':
    raise SystemExit(main())
