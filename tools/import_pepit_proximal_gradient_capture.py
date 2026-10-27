#!/usr/bin/env python3
"""D9: read a prepared PEPit-like capture without trusting its producer.

Exact symbolic rows, actual scalar-leaf ordering (tau may be anywhere), and
actual constraint order are preserved. Only known diagonal zero rows are
inserted into the *template*, with D7 checking that coverage independently.
Every captured dual has one ordered entry; zero or negative weights are never
filtered. The numeric residual is an independent input, never recomputed.
No PEPit/solver is required for offline replay. Captures used in regressions
are explicitly SIMULATED; success does not authenticate a producer or JSON.
"""
from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
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
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep

FORMAT = 'leanpep-pepit-pg-capture-v1'
AS = 'LeanPEP.Adapters.ProximalGradientCapture'
SUPPORTED_PEPIT = '0.5.1'


@dataclass(frozen=True)
class Converted:
    capture: dict[str, Any]
    source: dict[str, Any]
    value_map: order.IndexMap
    captured_rows: tuple[gram.LinearExprSpec, ...]
    captured_objective: gram.LinearExprSpec
    approximate: dict[str, Any] | None
    prepared: prep.Prepared | None
    source_passed: bool


def logical_tags(T: int) -> list[dict[str, Any]]:
    return [dict(kind=k, i=i, j=j) for k,c in
        (('smoothPair',T+2),('convexPair',T+1)) for i in range(c) for j in range(c)] + [
        dict(kind='radius',i=None,j=None)]


def label_key(tag: dict[str, Any]) -> tuple:
    if tag['kind']=='performance': return ('performance',)
    t=tag['tag']; return (t['kind'],t['i'],t['j'])


def canonical_roles(T: int) -> tuple[list[str],list[str]]:
    return (['x_star','x0','g_star']+[f'g{i}' for i in range(T+1)]+[f's{i}' for i in range(1,T+1)],
        ['f_star']+[f'f{i}' for i in range(T+1)]+['h_star']+[f'h{i}' for i in range(1,T+1)])


def _permutation(canonical: list[str], actual: list[str], path: str) -> order.IndexMap:
    if len(actual)!=len(canonical) or len(set(actual))!=len(actual) or set(actual)!=set(canonical):
        raise ValueError(path+': unsupported, duplicate or missing leaf roles')
    return order.index_map(tuple(actual.index(x) for x in canonical))


def _drop_tau(e: gram.LinearExprSpec) -> gram.LinearExprSpec:
    if e.value_coeff[0]!=0:
        raise ValueError('ordinary row or metric depends on tau; cannot drop it')
    return gram.LinearExprSpec(e.const,e.value_coeff[1:],e.gram_coeff)


def convert(raw: Any, expected_steps: int | None=None) -> Converted:
    d=gram.require_object(raw,'$')
    gram.check_keys(d,'$',required=('format','producer','horizon','profile','basis_order','value_order',
        'smooth_samples','nonsmooth_samples','metric','objective','constraints','numerical','policy'))
    if d['format']!=FORMAT: raise ValueError('unsupported capture format')
    producer=gram.require_object(d['producer'],'$.producer')
    gram.check_keys(producer,'$.producer',required=('name','version','mode','wrapper','solver','status'))
    if producer['name']!='PEPit' or producer['version']!=SUPPORTED_PEPIT:
        raise ValueError('only the explicit PEPit 0.5.1 capture contract is supported')
    if producer['mode'] not in ('live_solver_capture','prepared_only','simulated_regression'):
        raise ValueError('unknown capture mode')
    for k in ('name','version','mode','wrapper','solver','status'):
        gram.require_string(producer[k],'$.producer.'+k)
    T=gram.require_int(d['horizon'],'$.horizon',minimum=1)
    if expected_steps is not None and T!=expected_steps: raise ValueError('caller-selected horizon mismatch')
    prep._policy(d['policy'])
    profile=gram.require_object(d['profile'],'$.profile')
    gram.check_keys(profile,'$.profile',required=('smooth_class','nonsmooth_class','L','step_size','radius_squared'))
    if profile['smooth_class']!='SmoothConvexFunction' or profile['nonsmooth_class']!='ConvexFunction':
        raise ValueError('unsupported function classes')
    for key in ('L','step_size','radius_squared'):
        if gram.parse_rational(profile[key],'$.profile.'+key)!=1:
            raise ValueError('D9 supports only exact unit '+key)
    bc,vc=canonical_roles(T); m,p=len(bc),len(vc)
    basis=list(gram.parse_labels(d['basis_order'],'$.basis_order'))
    values=list(gram.parse_labels(d['value_order'],'$.value_order'))
    pb=_permutation(bc,basis,'$.basis_order')
    _permutation(vc+['tau'],values,'$.value_order')
    sampled=[x for x in values if x!='tau']
    pv=_permutation(vc,sampled,'$.value_order')
    tau_map=_permutation(['tau']+sampled,values,'$.value_order')
    identity=order.index_map(tuple(range(m)))
    def parse_expr(x: Any,path: str) -> gram.LinearExprSpec:
        return gram.parse_linear_expr(x,path,p+1,m)
    def moved(e: gram.LinearExprSpec) -> gram.LinearExprSpec:
        return order.expr(tau_map,identity,e)
    metric=_drop_tau(moved(parse_expr(d['metric'],'$.metric')))
    obj=parse_expr(d['objective'],'$.objective')
    moved_obj=moved(obj)
    def samples(name: str,count: int) -> tuple[list[dict[str,Any]],order.IndexMap]:
        result=[]; logical=[]
        for i,x in enumerate(gram.require_array(d[name],'$.'+name)):
            loc=f'$.{name}[{i}]'; s=gram.require_object(x,loc)
            gram.check_keys(s,loc,required=('logical_index','value_index','position','oracle'))
            j=gram.require_int(s['logical_index'],loc+'.logical_index',minimum=0);logical.append(j)
            vi=gram.require_int(s['value_index'],loc+'.value_index',minimum=0)
            if vi>=p+1 or values[vi]=='tau': raise ValueError(loc+': invalid sample value reference')
            result.append(dict(value_index=tau_map.to_canonical[vi]-1,
                position=gram.parse_rational_vector(s['position'],loc+'.position',m),
                oracle=gram.parse_rational_vector(s['oracle'],loc+'.oracle',m)))
        if sorted(logical)!=list(range(count)): raise ValueError(name+': logical sample coverage mismatch')
        return result,order.index_map(tuple(logical.index(i) for i in range(count)))
    sm,ps=samples('smooth_samples',T+2); ns,pn=samples('nonsmooth_samples',T+1)
    tags=logical_tags(T); full_labels=[{'kind':'performance'}]+[{'kind':'base','tag':t} for t in tags]
    keys=[label_key(t) for t in full_labels]
    actual=[]; labels=[]; to_full=[]; seen=set(); names=set()
    for i,x in enumerate(gram.require_array(d['constraints'],'$.constraints')):
        loc=f'$.constraints[{i}]'; rec=gram.require_object(x,loc)
        gram.check_keys(rec,loc,required=('name','label','sense','expression'))
        name=gram.require_string(rec['name'],loc+'.name')
        if not name or name in names: raise ValueError('empty or duplicate constraint name')
        names.add(name)
        if rec['sense']!='leZero': raise ValueError('only prepared scalar inequalities <= 0 are supported')
        label=sparse._label(rec['label'],loc+'.label'); key=label_key(label)
        if key not in keys or key in seen: raise ValueError('extra or duplicate logical constraint')
        seen.add(key);to_full.append(keys.index(key));labels.append(label)
        actual.append(parse_expr(rec['expression'],loc+'.expression'))
    k=len(actual); backward=[None]*len(keys)
    for i,j in enumerate(to_full): backward[j]=i
    if backward[0] is None: raise ValueError('missing performance row')
    full=[]
    for j,tag in enumerate(tags,1):
        i=backward[j]
        if i is not None: full.append(_drop_tau(moved(actual[i])))
        elif tag['kind']!='radius' and tag['i']==tag['j']: full.append(centered.zero(p,m))
        else: raise ValueError('missing nonzero/logically required row '+str(tag))
    C,J=native.maps(m-1)
    # Only fixed rectangular coordinate metadata is constructed. All samples,
    # metrics and nonzero constraint coefficients are read from the capture.
    C=tuple(tuple(row[b] for b in pb.to_canonical) for row in C)
    J=tuple(J[b] for b in pb.to_canonical)
    header=dict(profile_id=centered.PROFILE,coordinates=native.COORDINATES,steps=T,
        value_count=p,basis_count=m,smoothness=Q(1),step_size=Q(1),radius_squared=Q(1),
        smooth_class='oneSmoothConvex',nonsmooth_class='convex',sense='geZero',basis_order=basis,
        value_order=sampled,constraint_order=tags)
    unit=dict(sense='leZero',scale=Q(1))
    origin=dict(mode='deterministic_regression_fixture' if producer['mode']=='simulated_regression'
        else 'external_exact_snapshot',description='D9 untrusted '+producer['mode']+
        '; producer identity is NOT authenticated; input is retained separately')
    base=dict(format=rows.FORMAT,horizon=T,origin=origin,multiplier_convention=rows.CONVENTION,
        ordering={a:dict(to_source=q.to_source,to_canonical=q.to_canonical) for a,q in
            dict(basis=pb,values=pv,smooth=ps,nonsmooth=pn,rows=order.index_map(tuple(range(len(tags))))).items()},
        row_rules=[unit for _ in tags],source=dict(header=header,smooth_samples=sm,nonsmooth_samples=ns,
            constraints=[native.expr_tree(e) for e in full],objective=native.expr_tree(metric),
            center_matrix=C,section_matrix=J))
    source=centered.exact_json(dict(format=sparse.FORMAT,coverage_contract=sparse.CONTRACT,base_source=base,
        performance_rule=unit,coverage=dict(to_full=to_full,from_full=backward),
        rows=[native.expr_tree(moved(e)) for e in actual],row_rules=[unit for _ in actual],
        row_labels=labels,objective=native.expr_tree(moved_obj)))
    scaffold=prep._source_scaffold(source,T)
    diagnostic=sparse.diagnose(scaffold)
    # Source-only validity excludes placeholder upper acceptance.
    source_passed=diagnostic['source_passed']
    approximate=None; prepared=None
    if d['numerical'] is not None:
        if producer['mode']=='prepared_only': raise ValueError('prepared-only input must not claim solver numbers')
        z=gram.require_object(d['numerical'],'$.numerical')
        gram.check_keys(z,'$.numerical',required=('bound','multipliers','residual'))
        bound=prep.decimal(z['bound'],'$.numerical.bound')[0]
        weights=gram.require_array(z['multipliers'],'$.numerical.multipliers')
        if len(weights)!=k: raise ValueError('must keep exactly one dual per prepared row, including zeros')
        weights=[prep.decimal(w,f'$.numerical.multipliers[{i}]')[0] for i,w in enumerate(weights)]
        S=gram.require_array(z['residual'],'$.numerical.residual')
        if len(S)!=m or any(not isinstance(row,list) or len(row)!=m for row in S):
            raise ValueError('residual dimensions must match the actual leaf basis')
        S=[[prep.decimal(q,f'$.numerical.residual[{i}][{j}]')[0] for j,q in enumerate(row)] for i,row in enumerate(S)]
        def exact_decimal(q: Q) -> str:
            # Symbolic objective coefficients in this narrow exporter are dyadic;
            # fail rather than round a non-terminating rational into D8 input.
            n,dn=q.numerator,q.denominator; a=b=0
            while dn%2==0: a+=1;dn//=2
            while dn%5==0: b+=1;dn//=5
            if dn!=1: raise ValueError('objective has a non-terminating decimal; unsupported by D8')
            t=max(a,b); scaled=abs(n)*2**(t-a)*5**(t-b); whole,tail=divmod(scaled,10**t)
            return ('-' if n<0 else '')+str(whole)+('.'+str(tail).zfill(t) if t else '')
        upper=dict(bound=bound,objective=dict(const=exact_decimal(moved_obj.const),
            value_coeff=[exact_decimal(q) for q in moved_obj.value_coeff],
            gram_coeff=[[exact_decimal(q) for q in row] for row in moved_obj.gram_coeff]),
            assumption_terms=[dict(index=i,weight=w) for i,w in enumerate(weights)],
            interp_terms=[],dual_matrix=S)
        approximate=dict(format=prep.FORMAT,numeric_convention=prep.NUMBERS,source=source,
            upper=upper,policy=copy.deepcopy(d['policy']))
        prepared=prep.prepare(approximate,T)
    elif producer['mode']=='live_solver_capture':
        raise ValueError('live-solver capture missing numerical output')
    return Converted(copy.deepcopy(d),source,tau_map,tuple(actual),obj,approximate,prepared,bool(source_passed))


def raw_binding_diagnostic(c: Converted, upper: gram.UpperSpec) -> dict[str,bool]:
    if c.capture['numerical'] is None: raise ValueError('no numerical trace')
    z=c.capture['numerical']; m=len(upper.dual_matrix)
    identity=order.index_map(tuple(range(m)))
    return dict(bound=upper.bound==prep.decimal(z['bound'],'bound')[1],
        objective=upper.objective==order.expr(c.value_map,identity,c.captured_objective),
        interpolation_empty=not upper.interp_terms,
        ordered_weights=[(t.index,t.weight) for t in upper.assumption_terms]==
            [(i,prep.decimal(q,'weight')[1]) for i,q in enumerate(z['multipliers'])],
        residual=upper.dual_matrix==tuple(tuple(prep.decimal(q,'residual')[1] for q in row) for row in z['residual']))


def trace_diagnostic(c: Converted, artifact: sparse.Artifact | None=None,
                     value_map: order.IndexMap | None=None) -> dict[str,bool]:
    a=artifact or (c.prepared.raw.artifact if c.prepared else prep._source_scaffold(c.source,c.capture['horizon']))
    p=value_map or c.value_map; m=len(a.objective.gram_coeff)
    pb=order.index_map(tuple(range(m)))
    return dict(permutation=p.valid(),rows=tuple(order.expr(p,pb,e) for e in c.captured_rows)==a.compact_rows,
        objective=order.expr(p,pb,c.captured_objective)==a.objective,
        rules=all(r.sense=='leZero' and r.scale==1 for r in a.compact_rules),
        source=sparse.diagnose(a)['source_passed'])

def render_module(c: Converted, namespace: str) -> str:
    if c.prepared is None: raise ValueError('prepared-only capture has no numerical trace/certificate')
    text=prep.render_module(c.prepared,namespace).replace(f'import {prep.AS}',f'import {AS}',1)
    ending='end '+namespace+'\n'; assert text.endswith(ending)
    p=c.prepared.raw.artifact; z=c.capture['numerical']; n=c.capture['horizon']-1;k=len(c.captured_rows)
    expr=lambda e:order._record(gram.render_linear_expr,e)
    ix=lambda j:f'⟨{j}, by decide +kernel⟩'
    value_map='{ toSource := '+order._array(c.value_map.to_source,ix)+', toCanonical := '+order._array(c.value_map.to_canonical,ix)+' }'
    fields=[f'def traceQ : {AS}.TraceQ {n} {k} :=', '  { values := '+value_map,
        '    rows := '+order._array(c.captured_rows,expr),'    objective := '+expr(c.captured_objective),
        '    bound := '+gram.lean_rat(prep.decimal(z['bound'],'bound')[1]),
        '    weights := '+gram.lean_vector([prep.decimal(q,'weight')[1] for q in z['multipliers']]),
        '    residual := '+gram.lean_matrix([[prep.decimal(q,'residual')[1] for q in row] for row in z['residual']]),'  }']
    return text[:-len(ending)]+'\n'+'\n'.join(fields)+'\n'+ending


def outputs(c: Converted, directory: Path, namespace: str) -> dict[Path,str]:
    gram.validate_namespace(namespace)
    dump=lambda x:json.dumps(x,indent=2,sort_keys=True)+'\n'
    report=dict(format='leanpep-pg-capture-report-v1',capture_sha256=gram.canonical_json_sha256(c.capture),
        producer_claim=c.capture['producer'],producer_authenticated=False,lean_checked=False,
        live_capture_performed_by_importer=False,source_passed=c.source_passed,
        original_tau_index=c.capture['value_order'].index('tau'),value_map=dict(
            to_source=c.value_map.to_source,to_canonical=c.value_map.to_canonical),
        actual_constraint_count=len(c.captured_rows),numerical_candidate_present=c.prepared is not None,
        omitted_template_rows_only_diagonal=True,dual_matrix_recomputed=False,negative_weights_filtered=False,
        source_coefficients_reconstructed=False,scope='unit PG; no extra/equality/LMI rows or dependent leaves')
    result={directory/'capture_input.json':dump(c.capture),directory/'source.json':dump(c.source)}
    if c.prepared is not None:
        result.update(prep.outputs(c.prepared,directory/'candidates',namespace))
        result[directory/'Capture.lean']=render_module(c,namespace)
        result[directory/'approximate.json']=dump(c.approximate)
        report['trace_checks']=trace_diagnostic(c)
        report['raw_binding_checks']=raw_binding_diagnostic(c,c.prepared.raw.artifact.upper)
        bound_to_capture = all(report['trace_checks'].values()) and all(report['raw_binding_checks'].values())
        report['raw_accepted']=bound_to_capture and c.prepared.report['raw_accepted_diagnostic']
        report['reconstructed_accepted']=bound_to_capture and c.prepared.report['reconstructed_joint_accepted_diagnostic']
    result[directory/'capture_report.json']=dump(report)
    return result


def main(argv: list[str] | None=None) -> int:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--expected-steps',type=int);ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--namespace',required=True);ap.add_argument('--require-reconstructed-pass',action='store_true')
    a=ap.parse_args(argv)
    try:
        c=convert(gram.load_json(a.input),a.expected_steps)
        out=outputs(c,a.output_dir,a.namespace)
        if any(p.resolve()==a.input.resolve() for p in out): raise ValueError('output would overwrite input')
        for p,s in out.items(): gram.atomic_write(p,s)
        ok=(c.prepared is not None and all(trace_diagnostic(c).values())
            and all(raw_binding_diagnostic(c,c.prepared.raw.artifact.upper).values())
            and c.prepared.report['reconstructed_joint_accepted_diagnostic'])
        print(json.dumps(dict(source_passed=c.source_passed,reconstructed_passed=bool(ok),lean_checked=False)))
        return 2 if a.require_reconstructed_pass and not ok else 0
    except (ValueError,ArithmeticError,OSError) as e:
        print('error: '+str(e),file=sys.stderr);return 1

if __name__=='__main__': raise SystemExit(main())
