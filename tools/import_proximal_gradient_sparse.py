#!/usr/bin/env python3
"""D7 exact sparse-row coverage, not heuristic constraint completion.

The input has an independently audited D5 base-source template, a performance
rule, and ACTUAL shorter raw rows with explicit partial-inverse coverage maps.
A full row may be omitted only when ALL its rational coefficients are zero.
No label inference, witness-evaluation tests, dual-weight tests, or general
redundancy solver. The only submitted certificate is the sparse certificate.
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
import import_proximal_gradient_performance as perf

FORMAT = 'leanpep-zero-covered-pg-v1'
CONTRACT = 'injective_rows_omitted_coefficientwise_zero_v1'
AS = 'LeanPEP.Adapters.ProximalGradientSparse'


@dataclass(frozen=True)
class Coverage:
    # Compact storage -> full D6 SOURCE storage, not canonical row numbers.
    to_full: tuple[int, ...]
    from_full: tuple[int | None, ...]

    def valid(self) -> bool:
        k, r = len(self.to_full), len(self.from_full)
        return (all(type(j) is int and 0 <= j < r for j in self.to_full)
            and all(i is None or type(i) is int and 0 <= i < k for i in self.from_full)
            and all(self.from_full[j] == i for i,j in enumerate(self.to_full))
            and all(i is None or self.to_full[i] == j for j,i in enumerate(self.from_full)))


@dataclass(frozen=True)
class Artifact:
    base: rows.Artifact  # The upper here is PRIVATE source-parser scaffolding.
    performance_rule: rows.Rule
    coverage: Coverage
    compact_rows: tuple[gram.LinearExprSpec, ...]
    compact_rules: tuple[rows.Rule, ...]
    compact_labels: tuple[dict[str, Any], ...]
    objective: gram.LinearExprSpec
    upper: gram.UpperSpec
    sha256: str


def expected_rows(b: rows.Artifact, pr: rows.Rule) -> tuple[gram.LinearExprSpec, ...]:
    s = b.ordered.payload.source
    return (rows.encode(pr,perf.link(s.objective)),)+tuple(map(perf.embed,s.constraints))


def expected_rules(a: Artifact) -> tuple[rows.Rule, ...]:
    return (a.performance_rule,)+a.base.rules


def expected_labels(b: rows.Artifact) -> tuple[dict[str, Any], ...]:
    return ({'kind':'performance'},)+tuple({'kind':'base','tag':dict(t)}
        for t in b.ordered.payload.source.header['constraint_order'])


def is_zero(e: gram.LinearExprSpec) -> bool:
    return e == centered.zero(len(e.value_coeff),len(e.gram_coeff))


def artifact_tree(a: Artifact) -> dict[str, Any]:
    return centered.exact_json(dict(format=FORMAT,coverage_contract=CONTRACT,
        base_source=perf._base_tree(a.base),
        performance_rule=dict(sense=a.performance_rule.sense,scale=a.performance_rule.scale),
        coverage=dict(to_full=a.coverage.to_full,from_full=a.coverage.from_full),
        rows=[native.expr_tree(e) for e in a.compact_rows],
        row_rules=[dict(sense=r.sense,scale=r.scale) for r in a.compact_rules],
        row_labels=a.compact_labels,objective=native.expr_tree(a.objective),upper=native.upper_tree(a.upper)))


def _rule(raw: Any,path: str) -> rows.Rule:
    d=gram.require_object(raw,path)
    gram.check_keys(d,path,required=('sense','scale'))
    if d['sense'] not in ('geZero','leZero'):
        gram.fail(path+'.sense','only geZero and leZero are supported')
    return rows.Rule(d['sense'],gram.parse_rational(d['scale'],path+'.scale'))


def _label(raw: Any,path: str) -> dict[str,Any]:
    d=gram.require_object(raw,path)
    if d.get('kind')=='performance':
        gram.check_keys(d,path,required=('kind',))
        return dict(d)
    gram.check_keys(d,path,required=('kind','tag'))
    if d['kind']!='base': gram.fail(path+'.kind','expected base or performance')
    t=gram.require_object(d['tag'],path+'.tag')
    gram.check_keys(t,path+'.tag',required=('kind','i','j'))
    if t['kind'] not in ('smoothPair','convexPair','radius'):
        gram.fail(path+'.tag.kind','unknown logical row kind')
    out={'kind':t['kind']}
    for key in ('i','j'):
        out[key]=None if t[key] is None else gram.require_int(t[key],path+'.tag.'+key,minimum=0)
    return dict(kind='base',tag=out)


def parse_artifact(raw: Any, expected_steps: int | None=None) -> Artifact:
    d=gram.require_object(raw,'$')
    gram.check_keys(d,'$',required=('format','coverage_contract','base_source','performance_rule',
        'coverage','rows','row_rules','row_labels','objective','upper'))
    if d['format']!=FORMAT: gram.fail('$.format','unsupported sparse-row format')
    if d['coverage_contract']!=CONTRACT: gram.fail('$.coverage_contract','unsupported omission semantics')
    b=gram.require_object(d['base_source'],'$.base_source')
    gram.check_keys(b,'$.base_source',required=('format','horizon','origin','source','ordering','row_rules','multiplier_convention'))
    T=gram.require_int(b['horizon'],'$.base_source.horizon',minimum=1)
    dims=order.dimensions(T); p,m,r=dims['values'],dims['basis'],dims['rows']+1
    # Only source validation is reused; no base certificate is accepted as input.
    scaffold=centered.exact_json(native.upper_tree(perf._empty_upper(p,m)))
    base=rows.parse_artifact(dict(b,upper=scaffold),expected_steps)
    base=replace(base,sha256=gram.canonical_json_sha256(b))
    pr=_rule(d['performance_rule'],'$.performance_rule')
    xs=gram.require_array(d['rows'],'$.rows'); k=len(xs)
    cs=gram.require_object(d['coverage'],'$.coverage')
    gram.check_keys(cs,'$.coverage',required=('to_full','from_full'))
    f=gram.require_array(cs['to_full'],'$.coverage.to_full')
    g=gram.require_array(cs['from_full'],'$.coverage.from_full')
    if len(f)!=k or len(g)!=r: gram.fail('$.coverage','coverage arrays must have exactly k and full-row-count entries')
    fw=[]; bw=[]
    for i,v in enumerate(f):
        j=gram.require_int(v,f'$.coverage.to_full[{i}]',minimum=0)
        if j>=r: gram.fail(f'$.coverage.to_full[{i}]','out-of-range full row')
        fw.append(j)
    for j,v in enumerate(g):
        if v is None: bw.append(None); continue
        i=gram.require_int(v,f'$.coverage.from_full[{j}]',minimum=0)
        if i>=k: gram.fail(f'$.coverage.from_full[{j}]','out-of-range compact row')
        bw.append(i)
    rr=gram.require_array(d['row_rules'],'$.row_rules'); ls=gram.require_array(d['row_labels'],'$.row_labels')
    if len(rr)!=k or len(ls)!=k: gram.fail('$.rows','row/rule/label lengths must be identical')
    return Artifact(base,pr,Coverage(tuple(fw),tuple(bw)),
        tuple(gram.parse_linear_expr(e,f'$.rows[{i}]',p+1,m) for i,e in enumerate(xs)),
        tuple(_rule(e,f'$.row_rules[{i}]') for i,e in enumerate(rr)),
        tuple(_label(e,f'$.row_labels[{i}]') for i,e in enumerate(ls)),
        gram.parse_linear_expr(d['objective'],'$.objective',p+1,m),
        gram.parse_upper(d['upper'],'$.upper',p+1,m,k),gram.canonical_json_sha256(d))


def compact_snapshot(a: Artifact) -> centered.Snapshot:
    return replace(a.base.ordered.payload.source,objective=a.objective,
        constraints=tuple(rows.orient(a.compact_rules[i],e) for i,e in enumerate(a.compact_rows)))


def completed_artifact(a: Artifact) -> perf.Artifact:
    """Total candidate map, NOT source acceptance. No renormalization or repair.

    Keeps each supplied term (including zeros/duplicates) and only remaps its
    index. Incorrect coverage is rejected separately, not fixed by this function.
    """
    c=replace(a.upper,assumption_terms=tuple(replace(t,index=a.coverage.to_full[t.index])
        for t in a.upper.assumption_terms))
    out=perf.Artifact(a.base,a.performance_rule,expected_rows(a.base,a.performance_rule),a.objective,c,'')
    return replace(out,sha256=gram.canonical_json_sha256(perf.artifact_tree(out)))


def coverage_diagnostic(a: Artifact) -> dict[str, Any]:
    full=expected_rows(a.base,a.performance_rule); rr=expected_rules(a); ls=expected_labels(a.base)
    bad_rows=[i for i,j in enumerate(a.coverage.to_full) if a.compact_rows[i]!=full[j]]
    bad_rules=[i for i,j in enumerate(a.coverage.to_full) if a.compact_rules[i]!=rr[j]]
    bad_labels=[i for i,j in enumerate(a.coverage.to_full) if a.compact_labels[i]!=ls[j]]
    omitted=[j for j,i in enumerate(a.coverage.from_full) if i is None]
    nonzero=[j for j in omitted if not is_zero(full[j])]
    guards=dict(partial_inverse=a.coverage.valid(),retained_rows=not bad_rows,
        retained_rules=not bad_rules,retained_labels=not bad_labels,omitted_rows_zero=not nonzero)
    return dict(guards=guards,passed=all(guards.values()),omitted_full_indices=omitted,
        nonzero_omitted_indices=nonzero,row_mismatches=bad_rows,rule_mismatches=bad_rules,label_mismatches=bad_labels)


def diagnose(a: Artifact) -> dict[str, Any]:
    cd=coverage_diagnostic(a); full=completed_artifact(a); fd=perf.diagnose(full)
    local=native.local_check(compact_snapshot(a),a.upper)
    src=all(fd['bound_guards'][key] for key in ('base_source','positive_performance_scale','all_extended_rows','auxiliary_objective'))
    guards=dict(coverage=cd['passed'],full_source=src,compact_upper=local['accepted'],
        empty_implicit_interpolation=not a.upper.interp_terms,objective_binding=a.upper.objective==a.objective,
        full_bound=fd['diagnostic_passed'])
    return dict(format='leanpep-zero-row-coverage-diagnostic-v1',horizon=a.base.ordered.payload.horizon,
        canonical_json_sha256=a.sha256,origin=a.base.ordered.payload.origin,
        compact_row_count=len(a.compact_rows),full_row_count=len(a.coverage.from_full),coverage=cd,
        bound_guards=guards,source_passed=cd['passed'] and src,compact_certificate=local,completed_diagnostic=fd,
        term_count_preserved=len(a.upper.assumption_terms)==len(full.upper.assumption_terms),
        weights_preserved=[t.weight for t in a.upper.assumption_terms]==[t.weight for t in full.upper.assumption_terms],
        mapped_full_indices=[t.index for t in full.upper.assumption_terms],
        diagnostic_passed=all(guards.values()),lean_checked=False,live_capture_performed=False,
        provenance_authenticated=False,full_solver_pipeline_claimed=False,
        omitted_row_criterion='all_coefficients_zero_before_tau_and_origin_elimination',
        numeric_interpretation='exact_num_den_no_reconstruction')


def render_module(a: Artifact, namespace: str) -> str:
    gram.validate_namespace(namespace)
    prefix=rows.render_module(a.base,namespace+'.Base').split('def upperQ :',1)[0]
    prefix=prefix.replace(f'import {rows.AS}',f'import {AS}',1)
    prefix=prefix.replace('D5 generated exact signed/scaled raw data.', 'D7 base-source template, rendered with the unchanged D5 renderer.')
    prefix+=f'end {namespace}.Base\n\n'
    record=lambda e: order._record(gram.render_linear_expr,e)
    rule=lambda r: '{ sense := .'+r.sense+', scale := '+gram.lean_rat(r.scale)+' }'
    label=lambda t: '.performance' if t['kind']=='performance' else '.base '+order._record(centered._tag_lines,t['tag'])
    n=a.base.ordered.payload.horizon-1
    out=[prefix,f'namespace {namespace}',f'open LeanPEP.GramPEP {AS}',
        f'def sourceSha256 : String := {gram.lean_string(a.sha256)}',
        f'def sourceQ : SourceQ {n} {len(a.compact_rows)} :=',
        '  { base := Base.sourceQ',f'    performanceRule := {rule(a.performance_rule)}',
        '    coverage :=',
        '      { toFull := '+order._array(a.coverage.to_full,lambda j:f'⟨{j}, by decide +kernel⟩'),
        '        fromFull := '+order._array(a.coverage.from_full,lambda i:'none' if i is None else f'some ⟨{i}, by decide +kernel⟩'),
        '      }',
        '    rows := '+order._array(a.compact_rows,record),
        '    rules := '+order._array(a.compact_rules,rule),
        '    labels := '+order._array(a.compact_labels,label),
        '    objective := '+record(a.objective),'  }','']
    tmp=centered.Artifact(n+1,a.base.ordered.payload.origin,a.base.ordered.payload.source,a.upper,a.sha256)
    text=centered.render_module(tmp,namespace)
    out.append(text[text.index('def upperQ :'):])
    return '\n'.join(out)


def main(argv: list[str] | None=None) -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--expected-steps',type=int)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--report',type=Path,required=True)
    ap.add_argument('--namespace',required=True)
    ap.add_argument('--completed-json',type=Path)
    ap.add_argument('--require-diagnostic-pass',action='store_true')
    args=ap.parse_args(argv)
    paths=[args.input,args.lean,args.report]+([args.completed_json] if args.completed_json else [])
    if len({p.resolve() for p in paths})!=len(paths): ap.error('all input/output paths must be distinct')
    try:
        a=parse_artifact(gram.load_json(args.input),args.expected_steps)
        report=diagnose(a)
        # Otherwise an input with a missing nonzero row could be laundered into
        # a full-source artifact whose independent checker no longer sees the gap.
        if args.completed_json and not report['source_passed']:
            gram.fail('$.coverage','completion export requires exact source coverage and full source binding')
        gram.atomic_write(args.lean,render_module(a,args.namespace))
        gram.atomic_write(args.report,json.dumps(report,sort_keys=True,indent=2)+'\n')
        if args.completed_json:
            gram.atomic_write(args.completed_json,json.dumps(perf.artifact_tree(completed_artifact(a)),sort_keys=True,indent=2)+'\n')
        print('Python diagnostics:',report['diagnostic_passed'],'; Lean has NOT been run.')
        return 2 if args.require_diagnostic_pass and not report['diagnostic_passed'] else 0
    except (OSError,ValueError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 2


if __name__=='__main__':
    raise SystemExit(main())
