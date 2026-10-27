#!/usr/bin/env python3
"""D8: frozen exact composite source + two independently audited candidates.

All candidate scalars are finite decimal STRINGS. Raw means the exact decimal
rational, NOT the original binary float. Reconstruction is entrywise bounded-
denominator approximation with a fully recorded policy. Source coefficients,
labels, indices, scales, horizon and coverage never enter reconstruction.
The independent dual matrices are never recomputed from multipliers, repaired,
or symmetrized. D1 supplies exact factors or an exact failure witness per track.
No solver, known-rate lookup, acceptance assertion, or trusted JSON parser.
"""
from __future__ import annotations

import argparse
import copy
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
import import_proximal_gradient_performance as perf
import import_proximal_gradient_sparse as sparse
import prepare_approx_bundle as approx
import synthesize_psd_factors as psd

FORMAT = 'leanpep-approximate-pg-sparse-v1'
NUMBERS = 'finite_decimal_strings_v1'
AS = 'LeanPEP.Adapters.ProximalGradientReconstruction'
# Resource limits are syntactic, not mathematical tolerances. Never silently clip.
MAX_DECIMAL_LENGTH = 4096
MAX_DECIMAL_EXPONENT = 4096


@dataclass(frozen=True)
class Entry:
    path: str
    source: str
    raw: Q
    reconstructed: Q


@dataclass(frozen=True)
class Track:
    artifact: sparse.Artifact
    psd_result: psd.Result
    diagnostic: dict[str, Any]


@dataclass(frozen=True)
class Prepared:
    source: dict[str, Any]
    source_sha256: str
    policy: approx.ReconstructionPolicy
    entries: tuple[Entry, ...]
    raw: Track
    reconstructed: Track
    report: dict[str, Any]


def decimal(value: Any, path: str) -> tuple[str, Q]:
    if not isinstance(value, str) or len(value) > MAX_DECIMAL_LENGTH:
        raise ValueError(path + ': expected a bounded-length decimal string')
    # Avoid huge powers from hostile finite exponent strings, before Decimal/Fraction.
    exponent = value.lower().partition('e')[2]
    if exponent:
        try:
            if len(exponent) > 6 or abs(int(exponent)) > MAX_DECIMAL_EXPONENT:
                raise ValueError(path + ': decimal exponent outside supported resource bound')
        except ValueError as exc:
            raise ValueError(path + ': invalid or excessive decimal exponent') from exc
    return approx.parse_decimal_string(value, path)


def _policy(value: Any) -> approx.ReconstructionPolicy:
    d = gram.require_object(value, '$.policy')
    # Reuse the established policy contract, with bounded pre-parsing of its scalar.
    if 'max_abs_error' in d:
        decimal(d['max_abs_error'], '$.policy.max_abs_error')
    return approx.parse_policy(d)


def _source_scaffold(source: dict[str, Any], expected_steps: int | None) -> sparse.Artifact:
    if 'upper' in source:
        raise ValueError('$.source: submit exactly one approximate upper, not a base exact certificate')
    base = gram.require_object(source.get('base_source'), '$.source.base_source')
    T = gram.require_int(base.get('horizon'), '$.source.base_source.horizon', minimum=1)
    dims = order.dimensions(T)
    upper = centered.exact_json(native.upper_tree(perf._empty_upper(dims['values']+1, dims['basis'])))
    return sparse.parse_artifact(dict(source, upper=upper), expected_steps)


def source_tree(a: sparse.Artifact) -> dict[str, Any]:
    d = sparse.artifact_tree(a)
    del d['upper']
    return d


def _convert_upper(value: Any, policy: approx.ReconstructionPolicy, p: int, m: int,
                   k: int) -> tuple[gram.UpperSpec, gram.UpperSpec, tuple[Entry, ...]]:
    d = gram.require_object(value, '$.upper')
    gram.check_keys(d, '$.upper', required=('bound', 'objective', 'interp_terms',
        'assumption_terms', 'dual_matrix'))  # Factor hints are deliberately not a numerical input.
    entries: list[Entry] = []

    def number(v: Any, path: str) -> tuple[Q, Q]:
        text, raw = decimal(v, path)
        candidate = raw.limit_denominator(policy.max_denominator)
        entries.append(Entry(path, text, raw, candidate))
        return raw, candidate

    def vector(v: Any, path: str, n: int) -> tuple[tuple[Q,...], tuple[Q,...]]:
        xs = gram.require_array(v, path)
        if len(xs) != n:
            raise ValueError(f'{path}: expected exactly {n} entries')
        pairs = [number(x, f'{path}[{i}]') for i,x in enumerate(xs)]
        return tuple(a for a,_ in pairs), tuple(b for _,b in pairs)

    def matrix(v: Any, path: str) -> tuple[psd.Matrix, psd.Matrix]:
        xs = gram.require_array(v, path)
        if len(xs) != m:
            raise ValueError(f'{path}: expected exactly {m} rows')
        pairs = [vector(x, f'{path}[{i}]', m) for i,x in enumerate(xs)]
        return tuple(a for a,_ in pairs), tuple(b for _,b in pairs)

    def expr(v: Any, path: str) -> tuple[gram.LinearExprSpec, gram.LinearExprSpec]:
        x = gram.require_object(v, path)
        gram.check_keys(x,path,required=('const','value_coeff','gram_coeff'))
        c = number(x['const'], path+'.const')
        f = vector(x['value_coeff'],path+'.value_coeff',p)
        G = matrix(x['gram_coeff'],path+'.gram_coeff')
        return tuple(gram.LinearExprSpec(c[t],f[t],G[t]) for t in (0,1))  # type: ignore[return-value]

    bound = number(d['bound'],'$.upper.bound')
    objective = expr(d['objective'],'$.upper.objective')
    it: list[list[gram.InterpTermSpec]] = [[],[]]
    at: list[list[gram.AssumptionTermSpec]] = [[],[]]
    for j,v in enumerate(gram.require_array(d['interp_terms'],'$.upper.interp_terms')):
        path=f'$.upper.interp_terms[{j}]'
        t=gram.require_object(v,path); gram.check_keys(t,path,required=('i','j','weight'))
        i=gram.require_int(t['i'],path+'.i',minimum=0)
        jj=gram.require_int(t['j'],path+'.j',minimum=0)
        if i >= p or jj >= p: raise ValueError(path+': interpolation index out of range')
        w=number(t['weight'],path+'.weight')
        for a in (0,1): it[a].append(gram.InterpTermSpec(w[a],i,jj))
    for j,v in enumerate(gram.require_array(d['assumption_terms'],'$.upper.assumption_terms')):
        path=f'$.upper.assumption_terms[{j}]'
        t=gram.require_object(v,path); gram.check_keys(t,path,required=('index','weight'))
        i=gram.require_int(t['index'],path+'.index',minimum=0)
        if i >= k: raise ValueError(path+': assumption index out of range')
        w=number(t['weight'],path+'.weight')
        for a in (0,1): at[a].append(gram.AssumptionTermSpec(w[a],i))
    G=matrix(d['dual_matrix'],'$.upper.dual_matrix')
    empty=gram.FactorCertSpec(())
    return (gram.UpperSpec(bound[0],objective[0],tuple(it[0]),tuple(at[0]),G[0],empty),
        gram.UpperSpec(bound[1],objective[1],tuple(it[1]),tuple(at[1]),G[1],empty),tuple(entries))


def numerical_coefficients(c: gram.UpperSpec) -> tuple[Q,...]:
    e=c.objective
    return ((c.bound,e.const)+e.value_coeff+tuple(x for r in e.gram_coeff for x in r)
        +tuple(t.weight for t in c.interp_terms)+tuple(t.weight for t in c.assumption_terms)
        +tuple(x for r in c.dual_matrix for x in r))


def changes_diagnostic(policy: approx.ReconstructionPolicy, a: gram.UpperSpec,
                       b: gram.UpperSpec) -> dict[str,Any]:
    x,y=numerical_coefficients(a),numerical_coefficients(b)
    return dict(policy_valid=policy.max_denominator>0 and policy.max_abs_error>=0,
        assumption_references=[t.index for t in a.assumption_terms]==[t.index for t in b.assumption_terms],
        interpolation_references=[(t.i,t.j) for t in a.interp_terms]==[(t.i,t.j) for t in b.interp_terms],
        coefficient_lengths=len(x)==len(y),
        error_bounds=len(x)==len(y) and all(abs(j-i)<=policy.max_abs_error for i,j in zip(x,y)),
        denominator_bounds=all(q.denominator<=policy.max_denominator for q in y))


def _track(base: sparse.Artifact, c: gram.UpperSpec) -> Track:
    result=psd.synthesize_psd(c.dual_matrix)
    if not psd.verify_result(c.dual_matrix,result):
        raise ArithmeticError('D1 result failed independent exact recheck')
    # Negative/asymmetric targets KEEP THEIR ENTRIES. Empty factors permit a
    # total data carrier and are explicitly NOT a positive PSD result.
    fs=tuple(gram.RankOneFactorSpec(t.weight,t.vector) for t in result.factors) if result.status=='psd' else ()
    c=replace(c,dual_factor=gram.FactorCertSpec(fs))
    a=replace(base,upper=c,sha256='')
    a=replace(a,sha256=gram.canonical_json_sha256(sparse.artifact_tree(a)))
    return Track(a,result,sparse.diagnose(a))


def prepare(raw: Any, expected_steps: int | None=None) -> Prepared:
    d=gram.require_object(raw,'$')
    gram.check_keys(d,'$',required=('format','numeric_convention','source','policy','upper'))
    if d['format']!=FORMAT: raise ValueError('unsupported candidate format')
    if d['numeric_convention']!=NUMBERS: raise ValueError('unsupported numerical interpretation')
    src=copy.deepcopy(gram.require_object(d['source'],'$.source'))
    base=_source_scaffold(src,expected_steps)
    policy=_policy(d['policy'])
    p=len(base.objective.value_coeff); m=len(base.objective.gram_coeff)
    a,b,es=_convert_upper(d['upper'],policy,p,m,len(base.compact_rows))
    tracks=(_track(base,a),_track(base,b))
    # Exact parser canonicalization can reduce num/den, but may change NO value.
    sa,sb=map(lambda t:source_tree(t.artifact),tracks)
    if sa!=sb or sa!=source_tree(base): raise ArithmeticError('source mutation')
    cd=changes_diagnostic(policy,tracks[0].artifact.upper,tracks[1].artifact.upper)
    failures=[e.path for e in es if abs(e.reconstructed-e.raw)>policy.max_abs_error]
    entries=[dict(path=e.path,source=e.source,raw=psd.rat_json(e.raw),
        reconstructed=psd.rat_json(e.reconstructed),delta=psd.rat_json(e.reconstructed-e.raw),
        absolute_error=psd.rat_json(abs(e.reconstructed-e.raw)),
        within_error=abs(e.reconstructed-e.raw)<=policy.max_abs_error) for e in es]
    report=dict(format='leanpep-pg-reconstruction-report-v1',input_sha256=gram.canonical_json_sha256(d),
        source_sha256=gram.canonical_json_sha256(sa),source_unchanged=True,
        raw_interpretation=NUMBERS,policy=d['policy'],coefficient_count=len(es),
        changed_count=sum(e.raw!=e.reconstructed for e in es),entries=entries,
        change_guards=cd,out_of_budget_paths=failures,
        raw=dict(psd=psd.result_report(a.dual_matrix,tracks[0].psd_result),diagnostic=tracks[0].diagnostic),
        reconstructed=dict(psd=psd.result_report(b.dual_matrix,tracks[1].psd_result),diagnostic=tracks[1].diagnostic),
        raw_accepted_diagnostic=tracks[0].diagnostic['diagnostic_passed'],
        reconstructed_exact_accepted_diagnostic=tracks[1].diagnostic['diagnostic_passed'],
        reconstruction_policy_passed=all(cd.values()),
        reconstructed_joint_accepted_diagnostic=all(cd.values()) and tracks[1].diagnostic['diagnostic_passed'],
        lean_checked=False,live_capture_performed=False,provenance_authenticated=False,
        known_bound_used=False,matrix_repaired=False,source_reconstructed=False,
        factor_denominators_subject_to_policy=False,
        scope='exact frozen source; scalar upper candidates only; no primal, live capture, or soundness from proximity')
    if numerical_coefficients(a)!=tuple(e.raw for e in es) or numerical_coefficients(b)!=tuple(e.reconstructed for e in es):
        raise ArithmeticError('numeric traversal differs from the Lean audit order')
    return Prepared(sa,report['source_sha256'],policy,es,tracks[0],tracks[1],report)


def _upper_text(a: sparse.Artifact, namespace: str) -> str:
    # Use the original literal upper renderer, never regenerate a known certificate.
    tmp=centered.Artifact(a.base.ordered.payload.horizon,a.base.ordered.payload.origin,
        a.base.ordered.payload.source,a.upper,a.sha256)
    text=centered.render_module(tmp,namespace)
    return text[text.index('def upperQ :'):]


def render_module(p: Prepared, namespace: str) -> str:
    gram.validate_namespace(namespace)
    text=sparse.render_module(p.raw.artifact,namespace)
    text=text.replace(f'import {sparse.AS}',f'import {AS}',1)
    text=text.replace('def upperQ :','def rawUpperQ :',1)
    # The shared source hash excludes BOTH numerical certificates.
    old_hash='def sourceSha256 : String := '+gram.lean_string(p.raw.artifact.sha256)
    new_hash='def sourceSha256 : String := '+gram.lean_string(p.source_sha256)
    if text.count(old_hash)!=1: raise ValueError('upstream source hash renderer changed')
    text=text.replace(old_hash,new_hash,1)
    ending='end '+namespace+'\n'
    if not text.endswith(ending): raise ValueError('upstream namespace renderer changed')
    text=text[:-len(ending)]
    tail=_upper_text(p.reconstructed.artifact,namespace).replace('def upperQ :','def reconstructedUpperQ :',1)
    tail=tail[:-len(ending)]
    policy=('def policyQ : LeanPEP.GramPEP.RationalReconstructionAudit.PolicyQ :=\n'
        f'  {{ maxDenominator := {p.policy.max_denominator}\n'
        f'    maxAbsError := {gram.lean_rat(p.policy.max_abs_error)} }}\n')
    witness = ''
    if p.raw.psd_result.status == 'negative':
        w = p.raw.psd_result.witness
        if w is None: raise ArithmeticError('missing negative witness')
        witness = f'def rawNegativeVecQ : VecExpr {len(w)} ℚ := ' + gram.lean_vector(w) + '\n'
    return text+'\n'+tail+'\n'+policy+witness+ending


def outputs(p: Prepared, directory: Path, namespace: str) -> dict[Path,str]:
    out={directory/'Candidates.lean':render_module(p,namespace),
        directory/'report.json':json.dumps(p.report,indent=2,sort_keys=True)+'\n',
        directory/'source.json':json.dumps(p.source,indent=2,sort_keys=True)+'\n'}
    for name,t in (('raw',p.raw),('reconstructed',p.reconstructed)):
        out[directory/f'{name}_exact.json']=json.dumps(sparse.artifact_tree(t.artifact),indent=2,sort_keys=True)+'\n'
    return out


def main(argv: list[str] | None=None) -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--expected-steps',type=int)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--namespace',required=True)
    ap.add_argument('--require-reconstructed-pass',action='store_true')
    args=ap.parse_args(argv)
    try:
        p=prepare(gram.load_json(args.input),args.expected_steps)
        rendered=outputs(p,args.output_dir,args.namespace)
        if any(path.resolve()==args.input.resolve() for path in rendered):
            raise ValueError('output would overwrite the input; choose a different output directory')
        for path,text in rendered.items():
            gram.atomic_write(path,text)
        print(json.dumps({k:p.report[k] for k in ('raw_accepted_diagnostic',
            'reconstructed_exact_accepted_diagnostic','reconstruction_policy_passed',
            'reconstructed_joint_accepted_diagnostic','lean_checked')},sort_keys=True))
        return 2 if args.require_reconstructed_pass and not p.report['reconstructed_joint_accepted_diagnostic'] else 0
    except (ValueError, ArithmeticError, OSError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 1

if __name__=='__main__':
    raise SystemExit(main())
