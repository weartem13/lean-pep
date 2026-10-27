#!/usr/bin/env python3
"""D6 exact single-performance lifting, NOT a live solver or numeric repair tool.

The first scalar slot is tau and the first row encodes gamma*(metric-tau)>=0,
possibly in <=0 raw convention; gamma is strictly positive. The old value and
row storage order is preserved after the offset of one. No new Gram coordinate.
All extended rows and the objective are submitted and checked independently.
The importer never infers a missing row, fixes a dual, or sets tau to zero.
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
import import_proximal_gradient_rows as rows

FORMAT = 'leanpep-single-performance-pg-v1'
LAYOUT = 'tau_first_value_performance_first_row_v1'
AS = 'LeanPEP.Adapters.ProximalGradientPerformance'


@dataclass(frozen=True)
class Artifact:
    # Only the source portion of this parser carrier is read. Its auxiliary
    # zero upper is a private parsing scaffold, NEVER a submitted certificate.
    base: rows.Artifact
    performance_rule: rows.Rule
    extended_rows: tuple[gram.LinearExprSpec, ...]
    objective: gram.LinearExprSpec
    upper: gram.UpperSpec
    sha256: str


def embed(e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return replace(e, value_coeff=(Q(0),)+e.value_coeff)


def tau(p: int, m: int) -> gram.LinearExprSpec:
    if p < 0 or m < 0:
        raise ValueError('dimensions must be nonnegative')
    return replace(centered.zero(p+1,m), value_coeff=(Q(1),)+(Q(0),)*p)


def link(o: gram.LinearExprSpec) -> gram.LinearExprSpec:
    return centered.add(embed(o), centered.scale(Q(-1),tau(len(o.value_coeff),len(o.gram_coeff))))


def substitute(o: gram.LinearExprSpec, e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    """Substitute tau=o, preserving constant, value and ALL Gram contributions."""
    if len(e.value_coeff) != len(o.value_coeff)+1 or len(e.gram_coeff) != len(o.gram_coeff):
        raise ValueError('substitution dimension mismatch')
    tail = replace(e, value_coeff=e.value_coeff[1:])
    return centered.add(tail, centered.scale(e.value_coeff[0],o))


def _base_tree(b: rows.Artifact) -> dict[str, Any]:
    out=rows.artifact_tree(b)
    del out['upper']
    return out


def artifact_tree(a: Artifact) -> dict[str, Any]:
    return centered.exact_json(dict(format=FORMAT,layout=LAYOUT,base_source=_base_tree(a.base),
        performance_rule=dict(sense=a.performance_rule.sense,scale=a.performance_rule.scale),
        extended_rows=[native.expr_tree(e) for e in a.extended_rows],
        objective=native.expr_tree(a.objective),upper=native.upper_tree(a.upper)))


def _empty_upper(p: int, m: int) -> gram.UpperSpec:
    return gram.UpperSpec(Q(0),centered.zero(p,m),(),(),
        tuple((Q(0),)*m for _ in range(m)),gram.FactorCertSpec(()))


def parse_artifact(raw: Any, expected_steps: int | None=None) -> Artifact:
    d=gram.require_object(raw,'$')
    gram.check_keys(d,'$',required=('format','layout','base_source','performance_rule','extended_rows','objective','upper'))
    if d['format']!=FORMAT:
        gram.fail('$.format','unsupported performance format')
    if d['layout']!=LAYOUT:
        gram.fail('$.layout','only the declared single-auxiliary, first-slot layout is supported')
    b=gram.require_object(d['base_source'],'$.base_source')
    gram.check_keys(b,'$.base_source',required=('format','horizon','origin','source','ordering','row_rules','multiplier_convention'))
    T=gram.require_int(b['horizon'],'$.base_source.horizon',minimum=1)
    dims=order.dimensions(T)
    p,m,r=dims['values'],dims['basis'],dims['rows']
    # Reuse the unchanged D5 SOURCE validators. The private parser scaffold is
    # discarded by _base_tree/render_module and is never used for acceptance.
    lower=dict(b,upper=centered.exact_json(native.upper_tree(_empty_upper(p,m))))
    parsed=rows.parse_artifact(lower,expected_steps)
    parsed=replace(parsed,sha256=gram.canonical_json_sha256(b))
    rule=gram.require_object(d['performance_rule'],'$.performance_rule')
    gram.check_keys(rule,'$.performance_rule',required=('sense','scale'))
    if rule['sense'] not in ('geZero','leZero'):
        gram.fail('$.performance_rule.sense','must be geZero or leZero; no equality or strict inequality')
    pr=rows.Rule(rule['sense'],gram.parse_rational(rule['scale'],'$.performance_rule.scale'))
    xs=gram.require_array(d['extended_rows'],'$.extended_rows')
    if len(xs)!=r+1:
        gram.fail('$.extended_rows',f'exactly {r+1} rows are required; no truncation or missing-row filling')
    es=tuple(gram.parse_linear_expr(e,f'$.extended_rows[{i}]',p+1,m) for i,e in enumerate(xs))
    obj=gram.parse_linear_expr(d['objective'],'$.objective',p+1,m)
    c=gram.parse_upper(d['upper'],'$.upper',p+1,m,r+1)
    return Artifact(parsed,pr,es,obj,c,gram.canonical_json_sha256(d))


def oriented_snapshot(a: Artifact) -> centered.Snapshot:
    s=a.base.ordered.payload.source
    rs=(a.performance_rule,)+a.base.rules
    if len(rs)!=len(a.extended_rows):
        raise ValueError('extended rule/row count mismatch')
    return replace(s,constraints=tuple(rows.orient(rule,e) for rule,e in zip(rs,a.extended_rows)),
        objective=a.objective)


def eliminated_artifact(a: Artifact) -> rows.Artifact:
    """Total candidate map matching Lean. Sound use REQUIRES empty interpolation.

    No implicit interpolation on the auxiliary value is ever accepted. The CLI
    refuses to export base JSON for a nonempty implicit list, even at weight 0.
    Base-row indices are source indices minus ONE, before D5/D4 normalization.
    Only declared performance-row references (index zero) are removed.
    """
    b=a.base.ordered.payload
    c=replace(a.upper,objective=substitute(b.source.objective,a.upper.objective),interp_terms=(),
        assumption_terms=tuple(replace(t,index=t.index-1) for t in a.upper.assumption_terms if t.index!=0))
    out=replace(a.base,ordered=replace(a.base.ordered,payload=replace(b,upper=c)))
    return replace(out,sha256=gram.canonical_json_sha256(rows.artifact_tree(out)))


def _sum(s: centered.Snapshot,c: gram.UpperSpec) -> gram.LinearExprSpec:
    e=centered.zero(len(c.objective.value_coeff),len(c.dual_matrix))
    for t in c.assumption_terms:
        e=centered.add(e,centered.scale(t.weight,s.constraints[t.index]))
    return e


def diagnose(a: Artifact) -> dict[str, Any]:
    b=a.base.ordered.payload
    p,m=len(b.source.objective.value_coeff),len(b.source.objective.gram_coeff)
    expected=(rows.encode(a.performance_rule,link(b.source.objective)),)+tuple(map(embed,b.source.constraints))
    raw=oriented_snapshot(a)
    local=native.local_check(raw,a.upper)
    lowered=eliminated_artifact(a)
    ld=rows.diagnose(lowered)
    mismatch=[i for i,(x,y) in enumerate(zip(a.extended_rows,expected)) if x!=y]
    source_ok=ld['bound_guards']['positive_scales'] and ld['bound_guards']['normalized_source']
    guards=dict(base_source=source_ok,positive_performance_scale=a.performance_rule.scale>0,
        all_extended_rows=len(a.extended_rows)==len(expected) and not mismatch,
        auxiliary_objective=a.objective==tau(p,m),source_certificate=local['accepted'],
        empty_implicit_interpolation=not a.upper.interp_terms,
        certificate_objective=a.upper.objective==a.objective,eliminated_bound=ld['diagnostic_passed'])
    mass=sum((t.weight*a.performance_rule.scale for t in a.upper.assumption_terms if t.index==0),Q(0))
    rawsum=_sum(raw,a.upper)
    lowsum=_sum(rows.oriented_artifact(lowered).source,lowered.ordered.payload.upper)
    return dict(format='leanpep-single-performance-diagnostic-v1',horizon=b.horizon,
        canonical_json_sha256=a.sha256,origin=b.origin,
        dimensions=dict(base_values=p,extended_values=p+1,basis=m,base_rows=len(b.source.constraints),extended_rows=len(a.extended_rows)),
        layout=LAYOUT,bound_guards=guards,row_mismatches=mismatch,
        source_certificate=local,eliminated_diagnostic=ld,
        substituted_assumption_sum_preserved=substitute(b.source.objective,rawsum)==lowsum,
        performance_weighted_mass=centered.exact_json(mass),performance_mass_is_one=mass==1,
        removed_performance_references=sum(t.index==0 for t in a.upper.assumption_terms),
        retained_source_row_indices=[t.index-1 for t in a.upper.assumption_terms if t.index!=0],
        diagnostic_passed=all(guards.values()),lean_checked=False,live_capture_performed=False,
        provenance_authenticated=False,numeric_interpretation='exact_num_den_no_reconstruction',
        substitution='tau_equals_base_objective_not_zero',
        multiple_metrics_supported=False,arbitrary_auxiliary_order_supported=False,
        primal_import_supported=False,full_solver_pipeline_claimed=False)


def render_module(a: Artifact, namespace: str) -> str:
    gram.validate_namespace(namespace)
    # Render all submitted D5 base-source fields with the existing data renderer;
    # cut BEFORE its private scaffold upper and close the nested namespace.
    prefix=rows.render_module(a.base,namespace+'.Base').split('def upperQ :',1)[0]
    prefix=prefix.replace(f'import {rows.AS}',f'import {AS}',1)
    prefix=prefix.replace('D5 generated exact signed/scaled raw data.', 'D6 base-source data, rendered with the unchanged D5 renderer.')
    prefix+=f'end {namespace}.Base\n\n'
    n=a.base.ordered.payload.horizon-1
    record=lambda e: order._record(gram.render_linear_expr,e)
    rule='{ sense := .'+a.performance_rule.sense+', scale := '+gram.lean_rat(a.performance_rule.scale)+' }'
    out=[prefix,f'namespace {namespace}',f'open LeanPEP.GramPEP {AS}',
        f'def sourceSha256 : String := {gram.lean_string(a.sha256)}',
        f'def sourceQ : SourceQ {n} :=',
        '  { base := Base.sourceQ',f'    performanceRule := {rule}',
        '    rows := '+order._array(a.extended_rows,record),
        '    objective := '+record(a.objective),'  }','']
    # The old upper renderer is literal-data only and supports the supplied
    # extended dimension; no imported upper or known rate is substituted.
    tmp=centered.Artifact(n+1,a.base.ordered.payload.origin,a.base.ordered.payload.source,a.upper,a.sha256)
    text=centered.render_module(tmp,namespace)
    out.append(text[text.index('def upperQ :'):])
    return '\n'.join(out)


def main(argv: list[str] | None=None) -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--report',type=Path,required=True)
    ap.add_argument('--namespace',required=True)
    ap.add_argument('--expected-steps',type=int)
    ap.add_argument('--base-json',type=Path)
    ap.add_argument('--require-diagnostic-pass',action='store_true')
    args=ap.parse_args(argv)
    paths=[args.input,args.lean,args.report]+([args.base_json] if args.base_json else [])
    if len({p.resolve() for p in paths})!=len(paths):
        ap.error('all input/output paths must be distinct')
    try:
        a=parse_artifact(gram.load_json(args.input),args.expected_steps)
        if args.base_json and a.upper.interp_terms:
            gram.fail('$.upper.interp_terms','nonempty implicit interpolation cannot be exported to the reduced problem')
        text,report=render_module(a,args.namespace),diagnose(a)
        gram.atomic_write(args.lean,text)
        gram.atomic_write(args.report,json.dumps(report,indent=2,sort_keys=True)+'\n')
        if args.base_json:
            gram.atomic_write(args.base_json,json.dumps(rows.artifact_tree(eliminated_artifact(a)),indent=2,sort_keys=True)+'\n')
        print('Python diagnostics:',report['diagnostic_passed'],'; Lean has NOT been run.')
        return 2 if args.require_diagnostic_pass and not report['diagnostic_passed'] else 0
    except (ValueError,OSError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2


if __name__=='__main__':
    raise SystemExit(main())
