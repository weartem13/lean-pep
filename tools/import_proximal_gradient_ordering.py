#!/usr/bin/env python3
"""D4: explicit, checked permutations of exact D3-profile source storage.

No live capture, order inference, numeric reconstruction, row deletion/rescaling,
or general PEPit leaf elimination. Inputs remain untrusted. The generated Lean
module contains submitted arrays and bounded indices, NOT acceptance proofs.
Row-tag i/j are logical identifiers, not storage offsets into the sample arrays.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
import json
from pathlib import Path
import sys
from typing import Any, Callable, TypeVar

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_coordinates as native

FORMAT = 'leanpep-permuted-pg-source-v1'
AS = 'LeanPEP.Adapters.ProximalGradientOrdering'
AXES = ('basis', 'values', 'smooth', 'nonsmooth', 'rows')
A = TypeVar('A')


@dataclass(frozen=True)
class IndexMap:
    """to_source[canonical] = source; to_canonical[source] = canonical."""
    to_source: tuple[int, ...]
    to_canonical: tuple[int, ...]

    def valid(self) -> bool:
        k = len(self.to_source)
        return (len(self.to_canonical) == k
            and all(type(j) is int and 0 <= j < k for j in self.to_source+self.to_canonical)
            and all(self.to_canonical[self.to_source[i]] == i for i in range(k))
            and all(self.to_source[self.to_canonical[j]] == j for j in range(k)))

    def inverse(self) -> IndexMap:
        return IndexMap(self.to_canonical, self.to_source)


@dataclass(frozen=True)
class Artifact:
    payload: native.Artifact
    ordering: dict[str, IndexMap]
    sha256: str


def dimensions(T: int) -> dict[str, int]:
    p, _, q = native.dimensions(T)
    return dict(basis=q, values=p, smooth=T+2, nonsmooth=T+1, rows=(T+2)**2+(T+1)**2+1)


def index_map(p: tuple[int, ...]) -> IndexMap:
    """Convenience for fixture construction only; parsing never repairs inverse arrays."""
    if sorted(p) != list(range(len(p))):
        raise ValueError('not a permutation')
    back = [0]*len(p)
    for i, j in enumerate(p):
        back[j] = i
    return IndexMap(p, tuple(back))


def gather(o: IndexMap, xs: tuple[A, ...]) -> tuple[A, ...]:
    if len(xs) != len(o.to_source):
        raise ValueError('permutation/data dimension mismatch')
    return tuple(xs[i] for i in o.to_source)


def matrix(o: IndexMap, G: native.Matrix) -> native.Matrix:
    return tuple(tuple(G[i][j] for j in o.to_source) for i in o.to_source)


def expr(pv: IndexMap, pb: IndexMap, e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return replace(e, value_coeff=gather(pv, e.value_coeff), gram_coeff=matrix(pb, e.gram_coeff))


def sample(pv: IndexMap, pb: IndexMap, s: centered.Sample) -> centered.Sample:
    return centered.Sample(pv.to_canonical[s.value_index], gather(pb,s.position), gather(pb,s.oracle))


def transport(a: native.Artifact, o: dict[str, IndexMap]) -> native.Artifact:
    """Deterministic index transport; not an assertion that its input maps are valid."""
    s, c = a.source, a.upper
    pv, pb, pr = o['values'], o['basis'], o['rows']
    h = s.header.copy()
    h['basis_order'] = gather(pb, h['basis_order'])
    h['value_order'] = gather(pv, h['value_order'])
    h['constraint_order'] = gather(pr, h['constraint_order'])
    t = centered.Snapshot(h,
        tuple(sample(pv,pb,s.smooth_samples[i]) for i in o['smooth'].to_source),
        tuple(sample(pv,pb,s.nonsmooth_samples[i]) for i in o['nonsmooth'].to_source),
        tuple(expr(pv,pb,s.constraints[i]) for i in pr.to_source), expr(pv,pb,s.objective))
    d = replace(c, objective=expr(pv,pb,c.objective),
        interp_terms=tuple(replace(u,i=pv.to_canonical[u.i],j=pv.to_canonical[u.j]) for u in c.interp_terms),
        assumption_terms=tuple(replace(u,index=pr.to_canonical[u.index]) for u in c.assumption_terms),
        dual_matrix=matrix(pb,c.dual_matrix),
        dual_factor=gram.FactorCertSpec(tuple(replace(u,vector=gather(pb,u.vector)) for u in c.dual_factor.factors)))
    return replace(a, source=t, upper=d,
        center_matrix=tuple(gather(pb,row) for row in a.center_matrix),
        section_matrix=gather(pb,a.section_matrix))


def native_tree(a: native.Artifact) -> dict[str, Any]:
    return centered.exact_json(dict(format=native.FORMAT,horizon=a.horizon,origin=a.origin,
        source=dict(**centered.source_tree(a.source),center_matrix=a.center_matrix,section_matrix=a.section_matrix),
        upper=native.upper_tree(a.upper)))


def artifact_tree(a: Artifact) -> dict[str, Any]:
    d = native_tree(a.payload)
    d['format'] = FORMAT
    d['ordering'] = {k:dict(to_source=list(o.to_source),to_canonical=list(o.to_canonical))
                     for k,o in a.ordering.items()}
    return d


def parse_artifact(raw: Any, expected_steps: int | None = None) -> Artifact:
    d = gram.require_object(raw,'$')
    gram.check_keys(d,'$',required=('format','horizon','origin','source','upper','ordering'))
    if d['format'] != FORMAT:
        gram.fail('$.format','unsupported ordering format')
    lower = {k:v for k,v in d.items() if k != 'ordering'}
    lower['format'] = native.FORMAT
    a = native.parse_artifact(lower,expected_steps)
    dims = dimensions(a.horizon)
    lengths = dict(basis=len(a.source.header['basis_order']),values=len(a.source.header['value_order']),
        smooth=len(a.source.smooth_samples),nonsmooth=len(a.source.nonsmooth_samples),rows=len(a.source.constraints))
    for k in AXES:
        if lengths[k] != dims[k]:
            gram.fail('$.source.'+k,f'exact typed size must be {dims[k]}, got {lengths[k]}')
    if len(a.source.header['constraint_order']) != dims['rows']:
        gram.fail('$.source.header.constraint_order','length must equal the complete row count')
    orders = gram.require_object(d['ordering'],'$.ordering')
    gram.check_keys(orders,'$.ordering',required=AXES)
    result = {}
    for k in AXES:
        path = '$.ordering.'+k
        e = gram.require_object(orders[k],path)
        gram.check_keys(e,path,required=('to_source','to_canonical'))
        def indices(key: str) -> tuple[int, ...]:
            xs = gram.require_array(e[key],path+'.'+key)
            if len(xs) != dims[k]:
                gram.fail(path+'.'+key,f'expected {dims[k]} indices')
            out = tuple(gram.require_int(x,f'{path}.{key}[{i}]',minimum=0) for i,x in enumerate(xs))
            if any(x >= dims[k] for x in out):
                gram.fail(path+'.'+key,'index out of range')
            return out
        # In-range non-inverses remain representable candidates for independent rejection.
        result[k] = IndexMap(indices('to_source'),indices('to_canonical'))
    return Artifact(a,result,gram.canonical_json_sha256(d))


def canonical_native(a: Artifact) -> native.Artifact:
    # Do not reparse here: an in-range but nonbijective candidate may duplicate
    # labels in the transported output. Keep that candidate for rejection.
    b = transport(a.payload,a.ordering)
    return replace(b,sha256=gram.canonical_json_sha256(native_tree(b)))


def diagnose(a: Artifact) -> dict[str, Any]:
    valid = {k:p.valid() for k,p in a.ordering.items()}
    canonical = canonical_native(a)
    lower_error = None
    try:
        lower = native.diagnose(canonical)
    except ValueError as exc:
        # A malformed map may create a payload the older JSON reader refuses.
        # Rejection is recorded; the map and original data are never repaired.
        lower = None
        lower_error = str(exc)
    local = native.local_check(a.payload.source,a.payload.upper)
    restored = transport(transport(a.payload,a.ordering),{k:p.inverse() for k,p in a.ordering.items()})
    rt = native_tree(restored) == native_tree(a.payload)
    guards = dict(permutations=all(valid.values()),canonical_source=(lower is not None and all(lower['source_guards'].values())),
        source_certificate=local['accepted'],empty_implicit_interpolation=not a.payload.upper.interp_terms,
        source_objective=a.payload.upper.objective==a.payload.source.objective,
        canonical_bound=(lower is not None and lower['diagnostic_passed']))
    return dict(format='leanpep-permuted-pg-diagnostic-v1',horizon=a.payload.horizon,
        canonical_json_sha256=a.sha256,origin=a.payload.origin,dimensions=dimensions(a.payload.horizon),
        permutation_guards=valid,roundtrip_payload_and_certificate=rt,bound_guards=guards,
        source_certificate=local,canonical_diagnostic=lower,canonical_input_error=lower_error,
        diagnostic_passed=all(guards.values()),
        lean_checked=False,live_capture_performed=False,provenance_authenticated=False,
        row_tag_semantics='logical_component_point_indices_not_source_storage_offsets',
        coordinate_contract='five_bijective_storage_permutations_then_unchanged_D3_roundtrip_audit',
        arbitrary_pepit_leaf_elimination_supported=False,primal_import_supported=False,
        numeric_interpretation='exact_num_den_no_reconstruction')


def _array(xs: tuple[A, ...], render: Callable[[A], str]) -> str:
    return '!['+', '.join(render(x) for x in xs)+']'


def _index(i: int) -> str:
    return f'⟨{i}, by decide +kernel⟩'


def _record(render: Callable[[A], list[str]], x: A) -> str:
    # Inline the existing record literals to avoid offside ambiguity in vector syntax.
    lines = [line.strip() for line in render(x)]
    return ', '.join(lines) if len(lines) > 1 else lines[0]


def render_module(a: Artifact, namespace: str) -> str:
    gram.validate_namespace(namespace)
    s,c,h = a.payload.source,a.payload.upper,a.payload.source.header
    n=a.payload.horizon-1
    out=[f'import {AS}', '', '/-! D4 generated exact permuted data. No acceptance theorem is generated. -/',
        f'namespace {namespace}',f'open LeanPEP.GramPEP {AS}', '',
        f'def sourceSha256 : String := {gram.lean_string(a.sha256)}',
        f'def originMode : String := {gram.lean_string(a.payload.origin["mode"])}',
        f'def originDescription : String := {gram.lean_string(a.payload.origin["description"])}', '',
        f'def orderingQ : OrderingQ {n} :=', '  {']
    for k in AXES:
        o=a.ordering[k]
        out.append(f'    {k} := {{ toSource := '+_array(o.to_source,_index)+
            ', toCanonical := '+_array(o.to_canonical,_index)+' }')
    out += ['  }','',f'def snapshotQ : SnapshotQ {n} :=','  { metadata :=',
        '      { profileId := '+gram.lean_string(h['profile_id']),
        '        coordinates := '+gram.lean_string(h['coordinates'])]
    for field,key in (('steps','steps'),('valueCount','value_count'),('basisCount','basis_count')):
        out.append(f'        {field} := {h[key]}')
    for field,key in (('smoothness','smoothness'),('stepSize','step_size'),('radiusSquared','radius_squared')):
        out.append(f'        {field} := '+gram.lean_rat(h[key]))
    for field,key in (('smoothClass','smooth_class'),('nonsmoothClass','nonsmooth_class'),('sense','sense')):
        out.append(f'        {field} := .{h[key]}')
    out += ['      }','    basisLabels := '+_array(h['basis_order'],gram.lean_string),
        '    valueLabels := '+_array(h['value_order'],gram.lean_string),
        '    rowTags := '+_array(h['constraint_order'],lambda t:_record(centered._tag_lines,t)),
        '    centerMatrix := '+gram.lean_matrix(a.payload.center_matrix),
        '    sectionMatrix := '+gram.lean_matrix(a.payload.section_matrix),
        '    smoothSamples := '+_array(s.smooth_samples,lambda t:_record(centered._sample_lines,t)),
        '    nonsmoothSamples := '+_array(s.nonsmooth_samples,lambda t:_record(centered._sample_lines,t)),
        '    constraints := '+_array(s.constraints,lambda e:_record(gram.render_linear_expr,e)),
        '    objective := '+_record(gram.render_linear_expr,s.objective),
        '  }','',f'def sourceQ : SourceQ {n} :=', '  { ordering := orderingQ, snapshot := snapshotQ }','']
    # Reuse the original renderer for the upper's submitted data only.
    tmp = centered.Artifact(a.payload.horizon,a.payload.origin,s,c,a.sha256)
    old = centered.render_module(tmp,namespace)
    tail = old[old.index('def upperQ :'):]
    out.append(tail)
    return '\n'.join(out)


def main(argv: list[str] | None=None) -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--report',type=Path,required=True)
    ap.add_argument('--namespace',required=True)
    ap.add_argument('--expected-steps',type=int)
    ap.add_argument('--native-json',type=Path)
    ap.add_argument('--require-diagnostic-pass',action='store_true')
    args=ap.parse_args(argv)
    paths=[args.input,args.lean,args.report]+([args.native_json] if args.native_json else [])
    if len({p.resolve() for p in paths}) != len(paths):
        ap.error('all input/output paths must be distinct')
    try:
        a=parse_artifact(gram.load_json(args.input),args.expected_steps)
        text=render_module(a,args.namespace)
        report=diagnose(a)
        gram.atomic_write(args.lean,text)
        gram.atomic_write(args.report,json.dumps(report,indent=2,sort_keys=True)+'\n')
        if args.native_json:
            gram.atomic_write(args.native_json,json.dumps(native_tree(canonical_native(a)),indent=2,sort_keys=True)+'\n')
        print('Python diagnostics:',report['diagnostic_passed'],'; Lean has NOT been run.')
        return 2 if args.require_diagnostic_pass and not report['diagnostic_passed'] else 0
    except (ValueError,OSError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2


if __name__=='__main__':
    raise SystemExit(main())
