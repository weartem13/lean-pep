#!/usr/bin/env python3
"""GD1-only optimal-face producer; untrusted candidates gated by original Lean.
Uses fixed target 1/6 explicitly. Original APIs, policies, and stored files stay intact.
"""
from pathlib import Path
from fractions import Fraction as Q
from dataclasses import replace,asdict
from unittest.mock import patch
import argparse,json,re,subprocess,time
import replay_structured_gd_one as dual
import replay_primal_gd_one as primal
import import_exact_gram_bundle as gram
import run_pepit_pipeline as pipe
require=dual.require;write=dual.write
M=1000000;ETA=Q(1,M);ROOT=pipe.ROOT
RULE='gd1_source_optimal_face_target_one_sixth_v1'

def dual_family(c,a):
    rows,raw=dual.parse(c);b=Q(1,6);ws=[1,b,a,1-a,0,1-a,0,1-2*a]
    S=tuple(tuple(-raw.objective.gram_coeff[i][j]+sum(w*r.gram_coeff[i][j] for w,r in zip(ws,rows)) for j in range(3)) for i in range(3))
    fs=gram.FactorCertSpec((gram.RankOneFactorSpec(b,(Q(1),-3*a,-3*(1-a))),gram.RankOneFactorSpec(a*(2-3*a)/2,(Q(0),Q(1),Q(-1)))))
    return replace(raw,bound=b,assumption_terms=tuple(gram.AssumptionTermSpec(Q(w),i) for i,w in enumerate(ws)),dual_matrix=S,dual_factor=fs)

def exact_dual(c):
    _,raw=dual.parse(c)
    zero,one=dual_family(c,Q(0)),dual_family(c,Q(1))
    xs=dual.prep.numerical_coefficients(raw);zs=dual.prep.numerical_coefficients(zero);os=dual.prep.numerical_coefficients(one)
    intervals=[]
    for i,(x,z,o) in enumerate(zip(xs,zs,os)):
        k=o-z
        if not k:require(abs(z-x)<=ETA,'constant dual family budget '+str(i));continue
        ends=sorted(((x-ETA-z)/k,(x+ETA-z)/k));intervals.append(dict(index=i,lo=ends[0],hi=ends[1]))
    lo=max(i['lo'] for i in intervals);hi=min(i['hi'] for i in intervals);require(lo<=hi,'empty dual interval')
    a=((lo+hi)/2).limit_denominator(M//2);u=dual_family(c,a);audit=dual.audit(c,u)
    require(audit['accepted'],'original dual diagnostic rejection')
    return u,audit,dict(generation_rule='all32_affine_error_interval_midpoint_limit_denominator_v1',intervals=intervals,intersection=[lo,hi],a=a,target_bound=Q(1,6),known_rate_used=True,residual_recomputed=True)

def validate(c,s):
    dual.parse(c)
    require(s['format']=='leanpep-gd1-primal-observation-v1','primal schema')
    require(s['capture_sha256']==gram.canonical_json_sha256(c),'paired canonical source hash')
    require(s['basis_order']==c['basis_order'] and s['value_order']==c['value_order'] and s['tau_index']==3,'primal roles')
    require(s['source']=='PEPit.wrapper.get_primal_variables (optimal_G, optimal_F)','wrapper origin')
    require(s['numerical_convention']=='finite_decimal_strings_v1','decimal convention')
    for k in ['point_eval_used','projection_performed_by_exporter','feasibility_checked','lean_checked','actual_lower_bound_proved']:require(s[k] is False,'raw flags')
    require(len(s['gram'])==3 and all(len(r)==3 for r in s['gram']) and len(s['values'])==4,'dimensions')
    require(all(type(v)is str and '/' not in v for r in s['gram'] for v in r) and all(type(v)is str and '/' not in v for v in s['values']),'decimal strings')

def read_pair(cp,sp):
    c=gram.load_json(cp);s=gram.load_json(sp);validate(c,s)
    return c,s,primal.Datum(tuple(tuple(Q(v) for v in r) for r in s['gram']),tuple(map(Q,s['values'])))

def verify_live_archive(cp,sp):
    c,s,raw=read_pair(cp,sp)
    provenance=gram.load_json(cp.parent/'provenance.json')
    environment=gram.load_json(cp.parent/'environment.json')
    from capture_tight_gd_one import OPTIONS
    require(provenance['capture_byte_sha256']==pipe.digest(cp) and provenance['sidecar_byte_sha256']==pipe.digest(sp),'archive byte link')
    require(provenance['capture_canonical_sha256']==s['capture_sha256'],'archive canonical link')
    require(provenance['solve_count']==1 and provenance['live_capture_performed'] is True,'live source')
    require(c['producer']['options']==provenance['effective_solver_options']==environment['effective_solver_options']==OPTIONS,'effective solver options')
    require(all(provenance['effective_solve_kwargs'][k]==v for k,v in OPTIONS.items()),'actual solve kwargs')
    return c,s,raw

def audit(c,s,raw,d):
    # Reuse the existing numeric audit, with a scoped source-binding validator
    # for the NEW archive. This changes no Lean checker and no old default API.
    with patch.object(primal,'validate',validate),patch.object(primal,'RULE',RULE):return primal.audit(c,s,raw,d)

def exact_primal(c,s,raw):
    offsets=[Q(0),Q(5,18),Q(1,6)]
    lo=max(raw.F[i]-offsets[i]-ETA for i in range(3));hi=min(raw.F[i]-offsets[i]+ETA for i in range(3))
    require(lo<=hi,'empty value gauge interval')
    t=((lo+hi)/2).limit_denominator(M//18)
    G=((Q(1),Q(1,3),Q(1,3)),(Q(1,3),Q(1,9),Q(1,9)),(Q(1,3),Q(1,9),Q(1,9)))
    d=primal.Datum(G,(t,t+Q(5,18),t+Q(1,6),Q(1,6)))
    a=audit(c,s,raw,d)
    return d,a,dict(generation_rule=RULE,target_bound=Q(1,6),structure_from='source_identity_and_equality_conditions',known_rate_used=True,gauge_interval=[lo,hi],gauge=t,tau_rule='one_sixth_checked_directly',solver_calls=0)

def render_primal(c,s,raw,d,ns):
    with patch.object(primal,'validate',validate),patch.object(primal,'RULE',RULE):text=primal.render(c,s,raw,d,ns)
    # Old renderer prints diagnostics for its own archive; recompute both raw
    # diagnostics for this archive rather than asserting the old raw status.
    a=audit(c,s,raw,raw)
    text=text.replace('checkPSDFactorQ rawPrimalQ.gram rawFactorQ = true','checkPSDFactorQ rawPrimalQ.gram rawFactorQ = '+str(a['native_psd']).lower())
    rows,_=dual.parse(c);rows_ok=all(primal.evaluate(e,raw)<=0 for e in rows)
    text=text.replace('checkAssumptionsFeasibleQ nativeModelQ rawPrimalQ.data = false','checkAssumptionsFeasibleQ nativeModelQ rawPrimalQ.data = '+str(rows_ok).lower())
    return text

def invoke(cmd,log):
    start=time.monotonic();rc=pipe.invoke(cmd,log)
    return dict(cwd=str(ROOT),argv=cmd,exit=rc,log=str(log.relative_to(ROOT)),elapsed_seconds=time.monotonic()-start)

def run(kind,cp,sp,out,ns):
    require(not out.exists(),'new directory required');out.mkdir(parents=True)
    report=dict(kind=kind,selected=None,live_capture_performed=False,commands=[])
    write(out/'report.json',report)
    c=gram.load_json(cp)
    if kind=='dual':
        require(pipe.digest(cp)=='a2154f76e65a33c65a07631430b91c9d060cad8095b1598eec4fa319ad6fbc67','original dual bytes')
        u,a,g=exact_dual(c);payload=asdict(u);text=dual.render(c,u,ns).replace('set_option maxRecDepth','set_option autoImplicit false\nset_option maxRecDepth',1);name='Replay.lean';selected='selected_exact.json';adapter='LeanPEP.ActualFunction.GDOneCapture'
    else:
        c,s,raw=verify_live_archive(cp,sp);u,a,g=exact_primal(c,s,raw)
        write(out/'audit.json',a);write(out/'generation.json',g)
        require(a['candidate_diagnostic_accepted'],'primal rejected: '+str(a['first_failure']))
        payload=dict(format='leanpep-gd1-native-primal-v1',generation_rule=RULE,native_gram=u.G,native_values=u.F,source=c,audit=a)
        text=render_primal(c,s,raw,u,ns);name='PrimalReplay.lean';selected='selected_primal.json';adapter='LeanPEP.Adapters.GDOnePrimal'
    write(out/'input_link.json',dict(capture=str(cp.resolve()),capture_byte_sha256=pipe.digest(cp),capture_canonical_sha256=gram.canonical_json_sha256(c),sidecar=str(sp.resolve()) if sp else None,sidecar_byte_sha256=pipe.digest(sp) if sp else None))
    write(out/'audit.json',a);write(out/'generation.json',g);write(out/'candidate_unaccepted.json',payload)
    replay=out/name;replay.write_text(text)
    for cmd,log in [(['lake','build',adapter],'adapter_build.log'),(['lake','env','lean',str(replay.relative_to(ROOT))],'lean.log')]:
        rec=invoke(cmd,out/log);report['commands'].append(rec)
        if rec['exit']:report['status']='lean_failed';write(out/'report.json',report);return 2
    log=(out/'lean.log').read_text()
    matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
    require(matches and all({v.strip() for v in body.split(',') if v.strip()}<=pipe.ALLOWED_AXIOMS for _,body in matches) and 'sorryAx' not in log,'axioms')
    require((ns+'.actual_upper' in log) if kind=='dual' else primal.axioms_ok(log,ns),'required proofs printed')
    write(out/selected,payload);report.update(selected=selected,status='accepted',selected_sha256=pipe.digest(out/selected));write(out/'report.json',report);return 0
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('kind',choices=['dual','primal']);p.add_argument('--capture',type=Path,required=True);p.add_argument('--sidecar',type=Path);p.add_argument('--output',type=Path,required=True);p.add_argument('--namespace',required=True);a=p.parse_args();raise SystemExit(run(a.kind,a.capture,a.sidecar,a.output.resolve(),a.namespace))
