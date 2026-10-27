#!/usr/bin/env python3
"""GD(1)-specific untrusted source adapter / exact affine-grid producer / Lean gate."""
import argparse
from dataclasses import replace, asdict
from fractions import Fraction as Q
import hashlib
import json
import re
from pathlib import Path
from types import SimpleNamespace
import traceback
import import_exact_gram_bundle as gram
import import_proximal_gradient_source as algebra
import import_proximal_gradient_coordinates as mirror
import prepare_proximal_gradient_candidates as prep
import solve_exact_linear_system as linear
import synthesize_psd_factors as psd
import run_pepit_pipeline as pipeline

RULE='gd_one_source_affine_grid_v1'
PAIRS=[(i,j) for i in range(3) for j in range(3) if i!=j]
LABELS=[['performance'],['radius']]+[['smooth',i,j] for i,j in PAIRS]
POSITION=((0,0,0),(1,0,0),(1,-1,0))
GRADIENT=((0,0,0),(0,1,0),(0,0,1))
POLICY=SimpleNamespace(max_denominator=1000000,max_abs_error=Q(1,1000000))

def require(ok,msg):
    if not ok: raise ValueError(msg)

def exact(x):
    if isinstance(x,Q): return dict(num=x.numerator,den=x.denominator)
    if isinstance(x,dict): return {k:exact(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [exact(v) for v in x]
    return x

def write(path,data): pipeline.write_json(path,exact(data))

def expected():
    z=algebra.zero(4,3)
    value=lambda i: algebra.value(4,3,i)
    add,scale=algebra.add,algebra.scale
    metric=add(value(2),scale(-1,value(0)))
    rows=[add(value(3),scale(-1,metric)),replace(z,const=Q(-1),gram_coeff=((Q(1),Q(0),Q(0)),(Q(0),)*3,(Q(0),)*3))]
    for i,j in PAIRS:
        u=[Q(POSITION[i][k]-POSITION[j][k]) for k in range(3)]
        d=[Q(GRADIENT[i][k]-GRADIENT[j][k]) for k in range(3)]
        S=tuple(tuple((Q(GRADIENT[j][a])*u[b]+u[a]*Q(GRADIENT[j][b])+d[a]*d[b])/2 for b in range(3)) for a in range(3))
        rows.append(add(add(value(j),scale(-1,value(i))),replace(z,gram_coeff=S)))
    return metric,value(3),tuple(rows)

def parse(c):
    require(c['format']=='lean-pep-gd-one-capture-v1' and c['algorithm']=='smooth_only_gd','algorithm/schema')
    require(type(c['steps']) is int and c['steps']==1,'steps')
    require(c['profile']==dict(L='1',radius_squared='1',step_size='1',target='f1-f_star'),'profile/step/target')
    require(c['reference']==dict(position=['0']*3,gradient=['0']*3,rule='translate_reference_to_origin_and_stationarity'),'reference')
    require(c['basis_order']==['x0_minus_x_star','g0','g1'] and c['value_order']==['f_star','f0','f1','tau'],'native order')
    require(c['policy']==dict(max_denominator=1000000,max_abs_error='0.000001'),'original policy')
    require(len(c['samples'])==3,'sample count')
    for i,s in enumerate(c['samples']):
        require(s['value_index']==i and gram.parse_rational_vector(s['position'],'position',3)==POSITION[i] and gram.parse_rational_vector(s['gradient'],'gradient',3)==GRADIENT[i],'sample source')
    require([r['label'] for r in c['constraints']]==LABELS,'ordered labels/references')
    require(all(r['sense']=='leZero' for r in c['constraints']),'row sense')
    metric,obj,rows=expected()
    require(gram.parse_linear_expr(c['metric'],'metric',4,3)==metric,'metric source')
    require(gram.parse_linear_expr(c['objective'],'objective',4,3)==obj,'objective source')
    require(tuple(gram.parse_linear_expr(r['expression'],'row',4,3) for r in c['constraints'])==rows,'symbolic source coefficients')
    n=c['numerical']
    def decimal(s):
        require(isinstance(s,str) and '/' not in s,'raw finite decimal string required')
        return Q(s)
    require(len(n['multipliers'])==8 and len(n['residual'])==3 and all(len(row)==3 for row in n['residual']),'raw shape')
    raw=gram.UpperSpec(decimal(n['bound']),obj,(),tuple(gram.AssumptionTermSpec(decimal(w),i) for i,w in enumerate(n['multipliers'])),
        tuple(tuple(decimal(v) for v in r) for r in n['residual']),gram.FactorCertSpec(()))
    return rows,raw

def audit(c, candidate):
    rows,raw=parse(c)
    require(not candidate.interp_terms and [t.index for t in candidate.assumption_terms]==list(range(8)),'ordered candidate references')
    changes=prep.changes_diagnostic(POLICY,raw,candidate)
    local=mirror.local_check(SimpleNamespace(constraints=tuple(algebra.scale(-1,r) for r in rows)),candidate)
    xs,ys=prep.numerical_coefficients(raw),prep.numerical_coefficients(candidate)
    paths=['bound','objective.const']+[f'objective.value[{i}]' for i in range(4)]+[f'objective.gram[{i}][{j}]' for i in range(3) for j in range(3)]+[f'multiplier[{i}]' for i in range(8)]+[f'dual_matrix[{i}][{j}]' for i in range(3) for j in range(3)]
    require(len(xs)==len(ys)==len(paths)==32,'complete policy traversal')
    entries=[dict(path=p,raw=x,candidate=y,delta=y-x,absolute_error=abs(y-x),within_error=abs(y-x)<=POLICY.max_abs_error,denominator_within_policy=y.denominator<=1000000) for p,x,y in zip(paths,xs,ys)]
    return dict(policy=changes,original_upper_mirror=local,entries=entries,coefficient_count=len(xs),changed_count=sum(x!=y for x,y in zip(xs,ys)),
        max_abs_error=max(abs(y-x) for x,y in zip(xs,ys)),max_denominator=max(y.denominator for y in ys),factors_excluded_from_numeric_policy=True,
        accepted=all(changes.values()) and local['accepted'] and candidate.objective==raw.objective)

def generate(c):
    rows,raw=parse(c); o=raw.objective
    system=linear.System.make(9,[[Q(1)]+[e.const for e in rows]]+[[Q(0)]+[e.value_coeff[i] for e in rows] for i in range(4)],[o.const,*o.value_coeff])
    start=(raw.bound,)+tuple(t.weight for t in raw.assumption_terms)
    trials=[]
    for D in range(500000,499872,-1):
        def grid(v,up):
            n,d=v.numerator*D,v.denominator
            return Q(-(-n//d) if up else (2*n+d)//(2*d),D)
        seed=tuple(grid(v,i==2) for i,v in enumerate(start))
        r=linear.solve(system,seed); require(r.status=='solution','constant/value equations inconsistent')
        b,*weights=r.solution
        S=tuple(tuple(-o.gram_coeff[i][j]+sum(w*e.gram_coeff[i][j] for w,e in zip(weights,rows)) for j in range(3)) for i in range(3))
        u=replace(raw,bound=b,assumption_terms=tuple(gram.AssumptionTermSpec(w,i) for i,w in enumerate(weights)),dual_matrix=S)
        guards=prep.changes_diagnostic(POLICY,raw,u)
        trial=dict(denominator=D,policy=guards,nonnegative=all(w>=0 for w in weights));trials.append(trial)
        if not all(guards.values()) or not trial['nonnegative']: continue
        f=psd.synthesize_psd(S); require(psd.verify_result(S,f),'factor producer recheck')
        trial['psd']=psd.result_report(S,f)
        if f.status!='psd': continue
        u=replace(u,dual_factor=gram.FactorCertSpec(tuple(gram.RankOneFactorSpec(t.weight,t.vector) for t in f.factors)))
        a=audit(c,u)
        if a['accepted']:
            return u,a,dict(generation_rule=RULE,residual_recomputed=True,free_indices=list(r.free_columns),pivot_indices=list(r.pivot_columns),
                matrix=system.matrix,rhs=system.rhs,raw_seed=start,grid_seed=seed,solution=r.solution,max_trials=128,trial_count=len(trials),trials=trials,known_rate_used=False)
    raise ValueError('bounded GD candidate search exhausted (not infeasible)')

def render(c,u,namespace):
    gram.validate_namespace(namespace); require(audit(c,u)['accepted'],'candidate rejected')
    rows,raw=parse(c)
    expr=lambda e:', '.join(gram.render_linear_expr(e))
    rat,mat=gram.lean_rat,gram.lean_matrix
    def upper(name,a):
        terms=',\n'.join('{ weight := '+rat(t.weight)+', index := ⟨'+str(t.index)+', by decide +kernel⟩ }' for t in a.assumption_terms)
        factors=',\n'.join(', '.join(gram.render_factor(f)) for f in a.dual_factor.factors)
        return f'def {name} : UpperCertQ nativeModelQ :=\n{{ bound := {rat(a.bound)}, objective := {expr(a.objective)},\ninterpTerms := [], assumptionTerms := [{terms}],\ndualMatrix := {mat(a.dual_matrix)}, dualFactor := {{factors := [{factors}]}} }}\n'
    text=f'import LeanPEP.ActualFunction.GDOneCapture\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {namespace}\nopen LeanPEP.GramPEP LeanPEP.ActualFunction LeanPEP.ActualFunction.GDOneCapture\nopen LeanPEP.GramPEP.RationalReconstructionAudit\nopen scoped NNReal\n'
    text+=f'def sourceQ : SourceQ := {{position := {mat(POSITION)}, gradient := {mat(GRADIENT)}, rows := ['+',\n'.join(expr(e) for e in rows)+'],\nlabels := [(0,0,0),(1,0,0),(2,0,1),(2,0,2),(2,1,0),(2,1,2),(2,2,0),(2,2,1)],\nmetric := '+expr(expected()[0])+', objective := '+expr(raw.objective)+', steps := 1, stepSize := 1 }\n'
    text+='def traceQ : TraceQ := {bound := '+rat(raw.bound)+', multipliers := ['+','.join(rat(t.weight) for t in raw.assumption_terms)+'], residual := '+mat(raw.dual_matrix)+'}\n'
    text+='def policyQ : PolicyQ := {maxDenominator := 1000000, maxAbsError := 1/1000000}\n'+upper('rawUpperQ',raw)+upper('structuredUpperQ',u)
    text = re.sub(r'def .*?(?=\ndef |\Z)', lambda m: m.group(0).replace('\n', ' ')+'\n', text, flags=re.S)
    checks={'source_check':'checkSourceQ sourceQ','raw_check':'checkRawQ sourceQ traceQ rawUpperQ','policy_check':'checkChangesQ policyQ rawUpperQ structuredUpperQ','psd_check':'checkPSDFactorQ structuredUpperQ.dualMatrix structuredUpperQ.dualFactor','upper_check':'checkUpperCertQ structuredUpperQ','centered_check':'checkUpperCertQ (centered structuredUpperQ)','tau_rhs_transport':'checkLinearExprEqQ (eraseTau (certificateRhsExprQ structuredUpperQ)) (certificateRhsExprQ (centered structuredUpperQ))','tau_target_transport':'checkLinearExprEqQ (eraseTau (upperTargetExprQ structuredUpperQ.bound structuredUpperQ.objective)) (upperTargetExprQ (centered structuredUpperQ).bound (centered structuredUpperQ).objective)','accepted_check':'checkAcceptedQ sourceQ traceQ policyQ rawUpperQ structuredUpperQ'}
    for name,prop in checks.items():text+=f'theorem {name} : {prop} = true := by decide +kernel\n#print axioms {name}\n'
    text+=f'theorem bound_exact : structuredUpperQ.bound = {rat(u.bound)} := rfl\n'
    text+='''theorem actual_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar ≤ f y) (hstep : x1 = x0-(L : ℝ)⁻¹ • g x0)
    (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f x1-f xStar ≤ (L : ℝ)*R^2*(structuredUpperQ.bound : ℝ) :=
  GDOneCapture.upper_analytic sourceQ traceQ policyQ rawUpperQ structuredUpperQ accepted_check
    hf hL hR hmin hstep hradius
#print axioms actual_upper
#print axioms GDOneCapture.tau_substitution
#print axioms GDOneCapture.stationary_of_min
'''+f'end {namespace}\n'
    return text

def check_lean(replay, directory, namespace):
    # The thin module is deliberately not added to the old aggregate imports.
    code = pipeline.invoke(['lake','build','LeanPEP.ActualFunction.GDOneCapture'], directory/'lean_adapter_build.log')
    if code != 0:
        return dict(checked=False, adapter_build_exit=code, reason='adapter_build_failed')
    result = pipeline.check_lean(replay,directory,namespace,True)
    result['adapter_build_exit'] = code
    return result

def source_audit(c):
    rows,raw=parse(c)
    return dict(algorithm='smooth_only_gd',steps=1,source_passed=True,ordered_labels=LABELS,
        native_basis=c['basis_order'],native_values=c['value_order'],
        source_rows=[asdict(e) for e in rows],raw_upper=asdict(raw),
        gram_transport='identity: native basis is centered at capture construction',
        reference_gradient='exact symbolic zero; stationary_of_min derives analytic zero',
        tau_substitution='tau := f1-f_star; performance row becomes identically zero',
        all_eight_raw_multipliers_retained=True,centered_interpolation_order=PAIRS,
        centered_assumption='radius (native index 1)',
        live_capture_performed=False)

def run(capture_path,directory,namespace):
    require(not directory.exists() or not any(directory.iterdir()),'new/empty output directory required')
    directory.mkdir(parents=True,exist_ok=True)
    original=capture_path.read_bytes(); c=json.loads(original); parse(c)
    (directory/'capture.json').write_bytes(original)
    report=dict(capture_sha256=hashlib.sha256(original).hexdigest(),live_capture_performed=False,selected_endpoint=None,actual_upper_verified=False,generation_rule=RULE,residual_recomputed=True)
    write(directory/'report.json',report)
    write(directory/'source_trace_raw.json',source_audit(c))
    u,a,generation=generate(c)
    write(directory/'audit.json',a);write(directory/'generation.json',generation)
    write(directory/'candidate_unaccepted.json',asdict(u))
    (directory/'Replay.lean').write_text(render(c,u,namespace))
    result=check_lean(directory/'Replay.lean',directory,namespace)
    report['lean']=result
    report.update(primal_feasibility_checked=False,tightness_claimed=False,overall_v014a_accepted=False,proof_kind='actual_function_upper' if result['checked'] else None)
    if result['checked']:
        write(directory/'selected_exact.json',asdict(u))
        report.update(selected_endpoint='structured',actual_upper_verified=True,selected_sha256=pipeline.digest(directory/'selected_exact.json'),bound=exact(u.bound))
    write(directory/'report.json',report)
    require(result['checked'],'Lean did not accept; selected not published')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path,required=True);p.add_argument('--output-dir',type=Path,required=True);p.add_argument('--namespace',required=True);a=p.parse_args()
    try: print(json.dumps(run(a.capture,a.output_dir,a.namespace),indent=2))
    except Exception:
        traceback.print_exc();raise SystemExit(1)
