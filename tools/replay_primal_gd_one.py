#!/usr/bin/env python3
"""Archived GD1 wrapper finite primal: bounded untrusted repair, actual Lean gate.
Keeps the original gauge and checks every raw->candidate entry. No dual-rate seed.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import argparse,json,re,sys
import import_exact_gram_bundle as gram
import replay_structured_gd_one as source
import synthesize_psd_factors as psd
import run_pepit_pipeline as pipeline

ROOT=pipeline.ROOT
CAPTURE_SHA='a2154f76e65a33c65a07631430b91c9d060cad8095b1598eec4fa319ad6fbc67'
SIDECAR_SHA='eac439e2fef7b6abfcd1d4b05fec4f1afc76ecf902f74e9285da9000a667a776'
CANONICAL_SHA='9f3871037285b1b0fd841d006c679b8ff72710b6ec4676418fa4416f15facb17'
RULE='gd1_native_microgrid_then_equal_gradient_block_local9_v1'
ADAPTER='LeanPEP.Adapters.GDOnePrimal';M=1000000;ETA=Q(1,M)
require=source.require;write=source.write

@dataclass(frozen=True)
class Datum:
    G:tuple
    F:tuple

def validate(c,s):
    source.parse(c)
    require(s['format']=='leanpep-gd1-primal-observation-v1','primal schema')
    require(s['basis_order']==c['basis_order'] and s['value_order']==c['value_order'] and s['tau_index']==3,'primal roles/order')
    require(s['capture_sha256']==gram.canonical_json_sha256(c)==CANONICAL_SHA,'canonical source link')
    require(s['source']=='PEPit.wrapper.get_primal_variables (optimal_G, optimal_F)','wrapper origin')
    require(s['numerical_convention']=='finite_decimal_strings_v1','decimal convention')
    for k in ['point_eval_used','projection_performed_by_exporter','feasibility_checked','lean_checked','actual_lower_bound_proved']:require(s[k] is False,'raw flag changed')
    require(len(s['gram'])==3 and all(len(row)==3 for row in s['gram']) and len(s['values'])==4,'native dimensions')
    require(all(type(x)is str and '/' not in x for row in s['gram'] for x in row) and all(type(x)is str and '/' not in x for x in s['values']),'native decimals')

def read_inputs(cp,sp):
    require(pipeline.digest(cp)==CAPTURE_SHA,'capture byte hash')
    require(pipeline.digest(sp)==SIDECAR_SHA,'sidecar byte hash')
    c=gram.load_json(cp);s=gram.load_json(sp);validate(c,s)
    return c,s,Datum(tuple(tuple(Q(x) for x in row) for row in s['gram']),tuple(map(Q,s['values'])))

def evaluate(e,d):
    return e.const+sum(x*y for x,y in zip(e.value_coeff,d.F))+sum(e.gram_coeff[i][j]*d.G[i][j] for i in range(3) for j in range(3))

def factors(f):return [dict(weight=t.weight,vector=t.vector) for t in f.factors]

def audit(c,s,raw,d,factor=None):
    validate(c,s);rows,_=source.parse(c)
    require(len(d.G)==3 and all(len(row)==3 for row in d.G) and len(d.F)==4,'candidate dimensions')
    require(all(type(x)is Q for row in d.G for x in row) and all(type(x)is Q for x in d.F),'exact candidate only')
    entries=[dict(path=f'gram[{i}][{j}]',raw=raw.G[i][j],candidate=d.G[i][j]) for i in range(3) for j in range(3)]+[dict(path=f'values[{i}]',raw=raw.F[i],candidate=d.F[i]) for i in range(4)]
    for e in entries:e.update(delta=e['candidate']-e['raw'],absolute_error=abs(e['candidate']-e['raw']),denominator=e['candidate'].denominator,accepted=abs(e['candidate']-e['raw'])<=ETA and e['candidate'].denominator<=M)
    f=psd.synthesize_psd(d.G) if factor is None else factor
    vals=[evaluate(e,d) for e in rows];slacks=[]
    for i in range(3):
        for j in range(3):slacks.append(Q(0) if i==j else -vals[2+source.PAIRS.index((i,j))])
    beta=d.F[2]-d.F[0]
    ok=f.status=='psd' and psd.verify_result(d.G,f) and all(v<=0 for v in vals) and all(v>=0 for v in slacks) and beta>0 and d.F[3]<=beta and all(e['accepted'] for e in entries)
    first=next((e['path']+' budget' for e in entries if not e['accepted']),None)
    if first is None and f.status!='psd':first='native PSD: '+f.status
    if first is None:first=next((f'row[{i}]={v}>0' for i,v in enumerate(vals) if v>0),None)
    return dict(generation_rule=RULE,live_capture_performed=False,policy=dict(name='GD1_PRIMAL_POLICY_V1',M=M,eta=ETA,count=13,entries=entries,accepted=all(e['accepted'] for e in entries),max_error=max(entries,key=lambda e:e['absolute_error']),max_denominator=max(e['denominator'] for e in entries),changed_count=sum(e['raw']!=e['candidate'] for e in entries),factors_excluded=True),native_psd=f.status=='psd' and psd.verify_result(d.G,f),native_factor=factors(f),native_rows_leZero=vals,full_native_rows_geZero=[-vals[0],-vals[1]]+slacks,canonical_interpolation_slacks=slacks,radius_slack=-vals[1],canonical_gram=d.G,canonical_values=d.F[:3],beta=beta,tau=d.F[3],candidate_diagnostic_accepted=ok,first_failure=first)

def generate(c,s,raw):
    nearest=lambda x:Q(round(x*M),M)
    micro=Datum(tuple(tuple(nearest(x) for x in row) for row in raw.G),tuple(map(nearest,raw.F)))
    attempts=[]
    def trial(d,method,offset=None):
        a=audit(c,s,raw,d);attempts.append(dict(method=method,offset=offset,gram=d.G,values=d.F,first_failure=a['first_failure'],policy_accepted=a['policy']['accepted'],native_psd=a['native_psd'],rows=a['native_rows_leZero'],accepted=a['candidate_diagnostic_accepted']))
        return a
    a=trial(micro,'independent_all13_microgrid')
    if a['candidate_diagnostic_accepted']:return micro,a,attempts
    # Observed raw g0/g1 columns nearly coincide. This is only an untrusted local
    # candidate family; all entries and ALL inequalities are checked again.
    for da in (0,1,-1):
        for db in (0,1,-1):
            u=nearest(raw.G[0][1])+da*ETA;v=nearest(raw.G[1][1])+db*ETA
            G=((nearest(raw.G[0][0]),u,u),(u,v,v),(u,v,v))
            fs,f1=nearest(raw.F[0]),nearest(raw.F[2])
            d=Datum(G,(fs,f1+v,f1,min(nearest(raw.F[3]),f1-fs)))
            a=trial(d,'equal_gradient_block_and_f0_minus_f1_equals_norm_sq',(da,db))
            if a['candidate_diagnostic_accepted']:return d,a,attempts
    raise ValueError('bounded 1+9 candidate family exhausted; not global infeasibility')

def factor_lean(fs):
    return '{ factors := ['+', '.join('{ weight := '+gram.lean_rat(t['weight'])+', vector := '+gram.lean_vector(t['vector'])+' }' for t in fs)+'] }'

def render(c,s,raw,d,ns):
    gram.validate_namespace(ns);a=audit(c,s,raw,d);require(a['candidate_diagnostic_accepted'],'candidate rejected')
    rows,_=source.parse(c);rat,mat,vec=gram.lean_rat,gram.lean_matrix,gram.lean_vector
    expr=lambda e:', '.join(gram.render_linear_expr(e))
    text=f'import {ADAPTER}\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples\nopen LeanPEP.ActualFunction.GDOneCapture LeanPEP.Adapters\n'
    pos=tuple(gram.parse_rational_vector(t['position'],'position',3) for t in c['samples']);grad=tuple(gram.parse_rational_vector(t['gradient'],'gradient',3) for t in c['samples'])
    text+='def sourceQ : SourceQ := { position := '+mat(pos)+', gradient := '+mat(grad)+', rows := ['+', '.join(expr(r) for r in rows)+'], labels := [(0,0,0),(1,0,0),(2,0,1),(2,0,2),(2,1,0),(2,1,2),(2,2,0),(2,2,1)], metric := '+expr(source.expected()[0])+', objective := '+expr(source.expected()[1])+', steps := 1, stepSize := 1 }\n'
    for name,data in [('rawPrimalQ',raw),('candidateQ',d)]:text+=f'def {name} : GDOnePrimal.NativeQ := {{ gram := {mat(data.G)}, values := {vec(data.F)} }}\n'
    text+='def nativeFactorQ : PSDFactorCertQ 3 := '+factor_lean(a['native_factor'])+'\n'
    rf=psd.synthesize_psd(raw.G);text+='def rawFactorQ : PSDFactorCertQ 3 := '+factor_lean(factors(rf))+'\n'
    text+='def canonicalQ := GDOnePrimal.canonicalData candidateQ\n'
    rv=[evaluate(e,raw) for e in rows]
    checks={
      'source_check':'checkSourceQ sourceQ = true',
      'source_rows_binding':'sourceQ.rows.map RationalReconstructionAudit.exprCoefficientsQ = expectedRows.map RationalReconstructionAudit.exprCoefficientsQ',
      'policy_check':'GDOnePrimal.policy rawPrimalQ candidateQ = true',
      'native_psd_check':'checkPSDFactorQ candidateQ.gram nativeFactorQ = true',
      'raw_psd_check':'checkPSDFactorQ rawPrimalQ.gram rawFactorQ = true',
      'raw_rows_rejected':'checkAssumptionsFeasibleQ nativeModelQ rawPrimalQ.data = false',
      'raw_performance_value':'(expectedRows.get ⟨0, by decide +kernel⟩).evalQ rawPrimalQ.data = '+rat(rv[0]),
      'native_rows_check':'checkAssumptionsFeasibleQ nativeModelQ candidateQ.data = true',
      'full_rows_check':'checkAssumptionsFeasibleQ GDOnePrimal.fullNativeModelQ candidateQ.data = true',
      'model_check':'checkDataRealizesModelQ oneStepModelQ canonicalQ = true',
      'interpolation_check':'checkInterpolationFeasibleQ canonicalQ = true',
      'radius_check':'checkAssumptionsFeasibleQ oneStepModelQ canonicalQ = true',
      'finite_check':'GDOnePrimal.checkFinite candidateQ nativeFactorQ = true',
      'tau_beta':'candidateQ.values 3 ≤ GDOnePrimal.beta candidateQ',
      'beta_value':'GDOnePrimal.beta candidateQ = '+rat(a['beta']),
      'tau_value':'candidateQ.values 3 = '+rat(a['tau']),
      'counts':'expectedRows.length = 8 ∧ GDOnePrimal.fullNativeModelQ.assumptions.length = 11 ∧ (pointIndexPairs 3).length = 9 ∧ oneStepModelQ.assumptions.length = 1 ∧ (gramIndexPairs 3).length + (List.finRange 4).length = 13',
      'self_rows_zero':'∀ i : Fin 3, checkLinearExprEqQ (interpolationExprQ oneStepModelQ i i) (LinearExprQ.zero 3 3) = true',
      'native_gram_binding':'canonicalQ.gram = candidateQ.gram',
      'value_binding':'∀ i : Fin 3, canonicalQ.value i = candidateQ.values i.castSucc',
    }
    for n,prop in checks.items():text+=f'theorem {n} : {prop} := by decide +kernel\n'
    text+='''
theorem native_primal_checked : IsGramPosSemidef (castDataQ candidateQ.data).gram ∧
    AssumptionsFeasibleR nativeModelQ (castDataQ candidateQ.data) ∧
    AssumptionsFeasibleR GDOnePrimal.fullNativeModelQ (castDataQ candidateQ.data) := by
  have h := GDOnePrimal.checkFinite_sound candidateQ nativeFactorQ finite_check
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem finite_primal_verified :
    RealizesModelQ oneStepModelQ (castDataQ canonicalQ) ∧
    CoreFeasible (castDataQ canonicalQ) ∧
    AssumptionsFeasibleR oneStepModelQ (castDataQ canonicalQ) := by
  have h := GDOnePrimal.checkFinite_sound candidateQ nativeFactorQ finite_check
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem objective_verified : oneStepObjectiveQ.evalR (castDataQ canonicalQ) =
    (GDOnePrimal.beta candidateQ : ℝ) ∧ 0 < (GDOnePrimal.beta candidateQ : ℝ) := by
  have h := GDOnePrimal.checkFinite_sound candidateQ nativeFactorQ finite_check
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem concrete_primal_transport :
    (castDataQ canonicalQ).gram = (castDataQ candidateQ.data).gram ∧
    ∀ i : Fin 3, (castDataQ canonicalQ).value i = (candidateQ.values i.castSucc : ℝ) :=
  GDOnePrimal.primal_transport candidateQ
'''
    for n in [*checks,'native_primal_checked','finite_primal_verified','objective_verified','concrete_primal_transport']:text+='#print axioms '+n+'\n'
    text+='#print axioms GDOnePrimal.checkFinite_sound\n#print axioms GDOnePrimal.primal_transport\n'
    return text+'end '+ns+'\n'

def axioms_ok(log,ns):
    found={name:{v.strip() for v in body.split(',') if v.strip()} for name,body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log):found[n]=set()
    needed=['source_check','policy_check','native_psd_check','model_check','interpolation_check','finite_primal_verified','objective_verified','concrete_primal_transport']
    return all(ns+'.'+n in found for n in needed) and ADAPTER+'.checkFinite_sound' in found and all(s<=pipeline.ALLOWED_AXIOMS for s in found.values()) and 'sorryAx' not in log

def run(cp,sp,out,ns):
    require(not out.exists() or not any(out.iterdir()),'output must be new/empty');gram.validate_namespace(ns)
    c,s,raw=read_inputs(cp,sp);out.mkdir(parents=True,exist_ok=True)
    report=dict(task_id='LP-V014B-GD1-PRIMAL-001',namespace=ns,live_capture_performed=False,selected_primal=None,finite_primal_verified=False,objective_verified=False,actual_lower_bound_proved=False,actual_tightness=False,status='started',commands=[])
    write(out/'report.json',report)
    write(out/'input_link.json',dict(capture=str(cp.resolve()),sidecar=str(sp.resolve()),capture_byte_sha256=pipeline.digest(cp),sidecar_byte_sha256=pipeline.digest(sp),capture_canonical_sha256=CANONICAL_SHA,actual_live_directory='B14GDOnePrimalLive_001',old_upper_capture_not_used=True))
    write(out/'raw_audit.json',audit(c,s,raw,raw))
    d,a,attempts=generate(c,s,raw);write(out/'generation.json',dict(generation_rule=RULE,max_candidates=10,trial_count=len(attempts),trials=attempts,known_rate_used=False,solver_calls=0))
    payload=dict(format='leanpep-gd1-native-primal-v1',generation_rule=RULE,native_gram=d.G,native_values=d.F,source=c,audit=a)
    write(out/'candidate.json',payload);write(out/'direct_policy.json',a['policy'])
    replay=out/'PrimalReplay.lean';replay.write_text(render(c,s,raw,d,ns))
    for cmd,name in [(['lake','build',ADAPTER],'adapter_build.log'),(['lake','build','LeanPEP'],'library_build.log'),(['lake','env','lean','tests/lean/smoke/V13D13SmokeTest.lean'],'smoke.log'),(['lake','env','lean',str(replay.relative_to(ROOT))],'lean.log')]:
        log=out/name;rc=pipeline.invoke(cmd,log);report['commands'].append(dict(cwd=str(ROOT),argv=cmd,exit=rc,log=str(log.relative_to(ROOT)),log_sha256=pipeline.digest(log)))
        if rc:report['status']='lean_failed';write(out/'report.json',report);return report,2
    if not axioms_ok((out/'lean.log').read_text(),ns):report['status']='axiom_gate_failed';write(out/'report.json',report);return report,2
    write(out/'selected_primal.json',payload)
    report.update(status='finite_primal_verified',selected_primal='selected_primal.json',native_primal_checked=True,source_binding=True,model_realization=True,interpolation_checked=True,finite_primal_verified=True,objective_verified=True,axioms_allowed=True,beta=a['beta'],tau=a['tau'],selected_sha256=pipeline.digest(out/'selected_primal.json'),replay_sha256=pipeline.digest(replay))
    write(out/'report.json',report);return report,0

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path,default=ROOT/'data/cases/gd/one-step-gap/capture.json');p.add_argument('--sidecar',type=Path,default=ROOT/'data/cases/gd/one-step-gap/primal_observation.json');p.add_argument('--output',type=Path,required=True);p.add_argument('--namespace',required=True);a=p.parse_args()
    r,rc=run(a.capture,a.sidecar,a.output.resolve(),a.namespace);print(json.dumps(source.exact(r),indent=2));sys.exit(rc)
