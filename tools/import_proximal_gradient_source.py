#!/usr/bin/env python3
"""D2 untrusted exact centered PG snapshot importer and diagnostic mirror.

No solver, float parsing, rounding, coordinate conversion, row sorting or
coefficient repair. Rendering uses the submitted data, not expected_snapshot.
Only the separately compiled Lean checks can establish mathematical acceptance.
Old homogeneous ExactGramBundleQ is deliberately NOT used for composite values.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
from typing import Any

import import_exact_gram_bundle as gram
import synthesize_psd_factors as psd

FORMAT = 'leanpep-centered-pg-source-v1'
PROFILE = 'proximal-gradient-unit-positive-horizon-v1'
COORDINATES = 'centered-x0-gstar-gradients-residuals-v1'
AS = 'LeanPEP.Adapters.ProximalGradientSource'
HEADER_KEYS = ('profile_id', 'coordinates', 'steps', 'value_count', 'basis_count',
               'smoothness', 'step_size', 'radius_squared', 'smooth_class',
               'nonsmooth_class', 'sense', 'basis_order', 'value_order', 'constraint_order')


@dataclass(frozen=True)
class Sample:
    value_index: int
    position: tuple[Q, ...]
    oracle: tuple[Q, ...]


@dataclass(frozen=True)
class Snapshot:
    header: dict[str, Any]
    smooth_samples: tuple[Sample, ...]
    nonsmooth_samples: tuple[Sample, ...]
    constraints: tuple[gram.LinearExprSpec, ...]
    objective: gram.LinearExprSpec


@dataclass(frozen=True)
class Artifact:
    horizon: int
    origin: dict[str, str]
    source: Snapshot
    upper: gram.UpperSpec
    sha256: str


def dimensions(T: int) -> tuple[int, int]:
    if type(T) is not int or T < 1:
        raise ValueError('horizon must be a positive integer; bool is not an integer')
    return 2*T+3, 2*T+3


def _enum(value: Any, path: str, choices: tuple[str, ...]) -> str:
    s = gram.require_string(value, path)
    if s not in choices:
        gram.fail(path, 'expected one of ' + ', '.join(choices))
    return s


def parse_header(raw: Any) -> dict[str, Any]:
    path = '$.source.header'
    d = gram.require_object(raw, path)
    gram.check_keys(d, path, required=HEADER_KEYS)
    out: dict[str, Any] = {}
    for k in ('profile_id', 'coordinates'):
        out[k] = gram.require_string(d[k], path+'.'+k)
    for k in ('steps', 'value_count', 'basis_count'):
        out[k] = gram.require_int(d[k], path+'.'+k, minimum=0)
    for k in ('smoothness', 'step_size', 'radius_squared'):
        out[k] = gram.parse_rational(d[k], path+'.'+k)
    for k in ('smooth_class', 'nonsmooth_class'):
        out[k] = _enum(d[k], path+'.'+k, ('oneSmoothConvex', 'convex'))
    out['sense'] = _enum(d['sense'], path+'.sense', ('geZero', 'leZero'))
    for k in ('basis_order', 'value_order'):
        out[k] = gram.parse_labels(d[k], path+'.'+k)
    tags = []
    for a, item in enumerate(gram.require_array(d['constraint_order'], path+'.constraint_order')):
        loc = f'{path}.constraint_order[{a}]'
        obj = gram.require_object(item, loc)
        gram.check_keys(obj, loc, required=('kind', 'i', 'j'))
        kind = _enum(obj['kind'], loc+'.kind', ('smoothPair', 'convexPair', 'radius'))
        tags.append(dict(kind=kind, **{k: None if obj[k] is None else
            gram.require_int(obj[k], loc+'.'+k, minimum=0) for k in ('i', 'j')}))
    out['constraint_order'] = tuple(tags)
    return out


def parse_snapshot(raw: Any, T: int) -> Snapshot:
    p, m = dimensions(T)
    obj = gram.require_object(raw, '$.source')
    gram.check_keys(obj, '$.source', required=('header', 'smooth_samples',
        'nonsmooth_samples', 'constraints', 'objective'))
    def samples(name: str) -> tuple[Sample, ...]:
        out = []
        for k, x in enumerate(gram.require_array(obj[name], '$.source.'+name)):
            loc = f'$.source.{name}[{k}]'
            d = gram.require_object(x, loc)
            gram.check_keys(d, loc, required=('value_index', 'position', 'oracle'))
            i = gram.require_int(d['value_index'], loc+'.value_index', minimum=0)
            if i >= p:
                gram.fail(loc+'.value_index', 'out of range')
            out.append(Sample(i, gram.parse_rational_vector(d['position'], loc+'.position', m),
                              gram.parse_rational_vector(d['oracle'], loc+'.oracle', m)))
        return tuple(out)
    constraints = tuple(gram.parse_linear_expr(e, f'$.source.constraints[{k}]', p, m)
        for k, e in enumerate(gram.require_array(obj['constraints'], '$.source.constraints')))
    return Snapshot(parse_header(obj['header']), samples('smooth_samples'),
        samples('nonsmooth_samples'), constraints,
        gram.parse_linear_expr(obj['objective'], '$.source.objective', p, m))


def parse_artifact(raw: Any, expected_steps: int | None = None) -> Artifact:
    obj = gram.require_object(raw, '$')
    gram.check_keys(obj, '$', required=('format', 'horizon', 'origin', 'source', 'upper'))
    if obj['format'] != FORMAT:
        gram.fail('$.format', 'unsupported format')
    T = gram.require_int(obj['horizon'], '$.horizon', minimum=1)
    if expected_steps is not None and T != expected_steps:
        gram.fail('$.horizon', f'expected caller-selected horizon {expected_steps}')
    p, m = dimensions(T)
    origin = gram.require_object(obj['origin'], '$.origin')
    gram.check_keys(origin, '$.origin', required=('mode', 'description'))
    origin = dict(mode=_enum(origin['mode'], '$.origin.mode',
        ('deterministic_regression_fixture', 'external_exact_snapshot')),
        description=gram.require_string(origin['description'], '$.origin.description'))
    source = parse_snapshot(obj['source'], T)
    upper = gram.parse_upper(obj['upper'], '$.upper', p, m, len(source.constraints))
    return Artifact(T, origin, source, upper, gram.canonical_json_sha256(obj))


def zero(p: int, m: int) -> gram.LinearExprSpec:
    return gram.LinearExprSpec(Q(0), (Q(0),)*p, tuple((Q(0),)*m for _ in range(m)))


def scale(a: Q, x: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return gram.LinearExprSpec(a*x.const, tuple(a*t for t in x.value_coeff),
                              tuple(tuple(a*t for t in r) for r in x.gram_coeff))


def add(x: gram.LinearExprSpec, y: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return gram.LinearExprSpec(x.const+y.const,
        tuple(a+b for a, b in zip(x.value_coeff, y.value_coeff, strict=True)),
        tuple(tuple(a+b for a, b in zip(r, s, strict=True))
              for r, s in zip(x.gram_coeff, y.gram_coeff, strict=True)))


def unit(m: int, k: int) -> tuple[Q, ...]:
    if not 0 <= k < m:
        raise ValueError('unit index out of range')
    return tuple(Q(i == k) for i in range(m))


def vsub(x: tuple[Q, ...], y: tuple[Q, ...]) -> tuple[Q, ...]:
    return tuple(a-b for a, b in zip(x, y, strict=True))


def value(p: int, m: int, i: int) -> gram.LinearExprSpec:
    return gram.LinearExprSpec(Q(0), unit(p, i), zero(p, m).gram_coeff)


def bilinear(p: int, x: tuple[Q, ...], y: tuple[Q, ...]) -> gram.LinearExprSpec:
    m = len(x)
    return gram.LinearExprSpec(Q(0), (Q(0),)*p,
        tuple(tuple((x[i]*y[j]+x[j]*y[i])/2 for j in range(m)) for i in range(m)))


def pair(p: int, smooth: bool, a: Sample, b: Sample) -> gram.LinearExprSpec:
    m = len(a.position)
    out = add(add(value(p, m, a.value_index), scale(Q(-1), value(p, m, b.value_index))),
              scale(Q(-1), bilinear(p, b.oracle, vsub(a.position, b.position))))
    if smooth:
        d = vsub(a.oracle, b.oracle)
        out = add(out, scale(Q(-1, 2), bilinear(p, d, d)))
    return out


def expected_snapshot(T: int) -> Snapshot:
    """Untrusted Python diagnostic mirror. Never used to rewrite submitted arrays."""
    p, m = dimensions(T)
    xs = [unit(m, 0)]
    for k in range(T):
        xs.append(vsub(vsub(xs[-1], unit(m, k+2)), unit(m, T+3+k)))
    sm = (Sample(0, (Q(0),)*m, unit(m, 1)),) + tuple(
        Sample(k+1, xs[k], unit(m, k+2)) for k in range(T+1))
    ns = (Sample(T+2, (Q(0),)*m, tuple(-x for x in unit(m, 1))),) + tuple(
        Sample(T+3+k, xs[k+1], unit(m, T+3+k)) for k in range(T))
    cs = tuple(pair(p, True, a, b) for a in sm for b in sm) + tuple(
        pair(p, False, a, b) for a in ns for b in ns)
    radius = add(gram.LinearExprSpec(Q(1), (Q(0),)*p, zero(p, m).gram_coeff),
                 scale(Q(-1), bilinear(p, xs[0], xs[0])))
    obj = add(add(value(p, m, T+1), value(p, m, p-1)),
              scale(Q(-1), add(value(p, m, 0), value(p, m, T+2))))
    tags = tuple(dict(kind=kind, i=i, j=j) for kind, count in
                 (('smoothPair', T+2), ('convexPair', T+1))
                 for i in range(count) for j in range(count)) + (
                 dict(kind='radius', i=None, j=None),)
    header = dict(profile_id=PROFILE, coordinates=COORDINATES, steps=T,
        value_count=p, basis_count=m, smoothness=Q(1), step_size=Q(1), radius_squared=Q(1),
        smooth_class='oneSmoothConvex', nonsmooth_class='convex', sense='geZero',
        basis_order=tuple(['x0-x_star', 'g_star']+[f'g{k}' for k in range(T+1)]+[f's{k+1}' for k in range(T)]),
        value_order=tuple(['f_star']+[f'f{k}' for k in range(T+1)]+['h_star']+[f'h{k+1}' for k in range(T)]),
        constraint_order=tags)
    return Snapshot(header, sm, ns, cs+(radius,), obj)


def source_tree(s: Snapshot) -> dict[str, Any]:
    def sample(a: Sample) -> dict[str, Any]:
        return dict(value_index=a.value_index, position=a.position, oracle=a.oracle)
    def expr(e: gram.LinearExprSpec) -> dict[str, Any]:
        return dict(const=e.const, value_coeff=e.value_coeff, gram_coeff=e.gram_coeff)
    return dict(header=s.header, smooth_samples=tuple(map(sample, s.smooth_samples)),
                nonsmooth_samples=tuple(map(sample, s.nonsmooth_samples)),
                constraints=tuple(map(expr, s.constraints)), objective=expr(s.objective))


def exact_json(x: Any) -> Any:
    if isinstance(x, Q):
        return dict(num=x.numerator, den=x.denominator)
    if isinstance(x, dict):
        return {k: exact_json(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)):
        return [exact_json(v) for v in x]
    return x


def differences(expected: Any, actual: Any, path: str) -> list[dict[str, Any]]:
    if isinstance(expected, dict) and isinstance(actual, dict):
        return [d for k in expected for d in differences(expected[k], actual[k], path+'.'+k)]
    if isinstance(expected, (tuple, list)) and isinstance(actual, (tuple, list)):
        out = ([] if len(expected) == len(actual) else [dict(path=path+'.length',
                 expected=len(expected), actual=len(actual))])
        for k, (a, b) in enumerate(zip(expected, actual)):
            out.extend(differences(a, b, f'{path}[{k}]'))
        return out
    return [] if expected == actual else [dict(path=path, expected=exact_json(expected), actual=exact_json(actual))]


def diagnose(a: Artifact) -> dict[str, Any]:
    """Diagnostics only: full coefficient comparison, no Lean evaluation."""
    expected = source_tree(expected_snapshot(a.horizon))
    actual = source_tree(a.source)
    mismatches = differences(expected, actual, '$.source')
    c = a.upper
    p, m = dimensions(a.horizon)
    rhs = zero(p, m)
    for term in c.assumption_terms:
        rhs = add(rhs, scale(term.weight, a.source.constraints[term.index]))
    # The explicit carrier's dummy position/gradient vectors are all zero.
    # This mirrors the old checker, then a SEPARATE guard rejects all such terms.
    for term in c.interp_terms:
        rhs = add(rhs, scale(term.weight, add(value(p, m, term.i), scale(Q(-1), value(p, m, term.j)))))
    rhs = add(rhs, gram.LinearExprSpec(Q(0), (Q(0),)*p, c.dual_matrix))
    target = add(gram.LinearExprSpec(c.bound, (Q(0),)*p, zero(p, m).gram_coeff), scale(Q(-1), c.objective))
    factors = tuple(psd.Factor(t.weight, t.vector) for t in c.dual_factor.factors)
    factor_ok = (all(t.weight >= 0 for t in factors)
        and psd.reconstruct(m, factors) == c.dual_matrix
        and all(c.dual_matrix[i][j] == c.dual_matrix[j][i] for i in range(m) for j in range(m)))
    cert_ok = factor_ok and all(t.weight >= 0 for t in c.assumption_terms+c.interp_terms) and rhs == target
    guards = dict(source=not mismatches, certificate=cert_ok,
                  empty_implicit_interpolation=not c.interp_terms,
                  objective_matches_source=c.objective == a.source.objective)
    return dict(format='leanpep-centered-pg-diagnostic-v1', horizon=a.horizon, origin=a.origin,
        canonical_json_sha256=a.sha256, source_block_checks={k: expected[k] == actual[k] for k in expected},
        source_mismatches=mismatches, guards=guards, diagnostic_passed=all(guards.values()),
        upper_factor_diagnostic=factor_ok, upper_identity_diagnostic=(rhs == target),
        lean_checked=False, live_capture_performed=False, provenance_authenticated=False,
        native_coordinate_transform_checked=False, actual_lower_witness_checked=False,
        numeric_interpretation='exact_num_den_no_reconstruction')


def _sample_lines(s: Sample) -> list[str]:
    return [f'{{ valueIndex := {s.value_index}',
            '  position := '+gram.lean_vector(s.position),
            '  oracle := '+gram.lean_vector(s.oracle)+' }']


def _tag_lines(d: dict[str, Any]) -> list[str]:
    opt = lambda n: 'none' if n is None else f'some {n}'
    return [f'{{ kind := .{d["kind"]}, i := {opt(d["i"])}, j := {opt(d["j"])} }}']


def render_module(a: Artifact, namespace: str) -> str:
    """Emit submitted exact data only. Never emit an automatic acceptance theorem."""
    gram.validate_namespace(namespace)
    n = a.horizon-1
    h = a.source.header
    out = [f'import {AS}', '',
           '/-! D2 generated exact centered snapshot. No acceptance proof is generated. -/',
           f'namespace {namespace}', f'open LeanPEP.GramPEP {AS}', '',
           f'def sourceSha256 : String := {gram.lean_string(a.sha256)}',
           f'def originMode : String := {gram.lean_string(a.origin["mode"])}',
           f'def originDescription : String := {gram.lean_string(a.origin["description"])}', '',
           f'def sourceQ : SourceQ {n} :=', '  { header :=',
           '      { profileId := '+gram.lean_string(h['profile_id']),
           '        coordinates := '+gram.lean_string(h['coordinates'])]
    for field, key in (('steps', 'steps'), ('valueCount', 'value_count'), ('basisCount', 'basis_count')):
        out.append(f'        {field} := {h[key]}')
    for field, key in (('smoothness', 'smoothness'), ('stepSize', 'step_size'), ('radiusSquared', 'radius_squared')):
        out.append(f'        {field} := '+gram.lean_rat(h[key]))
    for field, key in (('smoothClass', 'smooth_class'), ('nonsmoothClass', 'nonsmooth_class'), ('sense', 'sense')):
        out.append(f'        {field} := .{h[key]}')
    for field, key in (('basisOrder', 'basis_order'), ('valueOrder', 'value_order')):
        out.append(f'        {field} := '+gram.lean_string_list(h[key]))
    out.append('        constraintOrder :=')
    out += gram.indent_lines(gram.render_record_list(h['constraint_order'], _tag_lines), 10)
    out.append('      }')
    for field, samples in (('smoothSamples', a.source.smooth_samples), ('nonsmoothSamples', a.source.nonsmooth_samples)):
        out.append(f'    {field} :=')
        out += gram.indent_lines(gram.render_record_list(samples, _sample_lines), 6)
    out.append('    constraints :=')
    out += gram.indent_lines(gram.render_record_list(a.source.constraints, gram.render_linear_expr), 6)
    out.append('    objective :=')
    out += gram.indent_lines(gram.render_linear_expr(a.source.objective), 6)
    out += ['  }', '', 'def upperQ : UpperCertQ sourceQ.model :=',
            '  { bound := '+gram.lean_rat(a.upper.bound), '    objective :=']
    out += gram.indent_lines(gram.render_linear_expr(a.upper.objective), 6)
    out += ['    interpTerms :=']
    out += gram.indent_lines(gram.render_record_list(a.upper.interp_terms, gram.render_interp_term), 6)
    out += ['    assumptionTerms :=']
    def term(t: gram.AssumptionTermSpec) -> list[str]:
        return ['{ weight := '+gram.lean_rat(t.weight)+f', index := ⟨{t.index}, by decide +kernel⟩ }}']
    out += gram.indent_lines(gram.render_record_list(a.upper.assumption_terms, term), 6)
    out += ['    dualMatrix := '+gram.lean_matrix(a.upper.dual_matrix), '    dualFactor :=', '      { factors :=']
    out += gram.indent_lines(gram.render_record_list(a.upper.dual_factor.factors, gram.render_factor), 8)
    out += ['      }', '  }', '', f'end {namespace}', '']
    return '\n'.join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--namespace', required=True)
    parser.add_argument('--expected-steps', type=int)
    parser.add_argument('--require-diagnostic-pass', action='store_true')
    args = parser.parse_args(argv)
    if len({p.resolve() for p in (args.input, args.lean, args.report)}) != 3:
        parser.error('input, Lean output, and report must be distinct paths')
    try:
        artifact = parse_artifact(gram.load_json(args.input), args.expected_steps)
        text = render_module(artifact, args.namespace)
        report = diagnose(artifact)
        gram.atomic_write(args.lean, text)
        gram.atomic_write(args.report, json.dumps(report, indent=2, sort_keys=True)+'\n')
        print('Python diagnostics:', report['diagnostic_passed'], '; Lean has NOT been run.')
        return 2 if args.require_diagnostic_pass and not report['diagnostic_passed'] else 0
    except (ValueError, OSError) as exc:
        print(f'error: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
