#!/usr/bin/env python3
"""005-only offline finite-primal recovery. Never solves or edits archived data.

Untrusted candidate: round EACH native decimal to nearest 10^-6 (ties-to-even).
No ideal witness, dual bound, active set, gauge change or dropped axis is used.
All 42 changes, every source constraint and both exact PSD factors are checked.
Publishing requires actual Lean execution, not these Python diagnostics.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import sys

import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import import_proximal_gradient_source as algebra
import replay_structured_pg_one as archive
import synthesize_psd_factors as psd
import run_pepit_pipeline as pipeline

ROOT=pipeline.ROOT
SIDECAR_SHA='bcb554e3eb8dca873f126f6fced3c84f31856ec12e9f0c22ae46b2b14edac79e'
CANONICAL_SHA='a6764b3e011a9659c16f3b2e430ccf64771bfbcef24c0edcac707f6f5e8f7d12'
VALUES=['f_star','h_star','f0','h1','f1','tau']
RULE='pg1_native_all42_nearest_microgrid_ties_even_v1'
M=1000000
ETA=Q(1,M)
ADAPTER='LeanPEP.Adapters.PGOnePrimal'
require=archive.require

@dataclass(frozen=True)
class Datum:
    G: tuple[tuple[Q,...],...]
    F: tuple[Q,...]


def write(path,data):
    pipeline.write_json(path,algebra.exact_json(data))


def validate(c,side):
    archive.validate_source(c)
    require(c.capture['value_order']==VALUES,'capture value order')
    require(side['format']=='leanpep-primal-observation-v1','primal sidecar format')
    require(side['basis_order']==archive.BASIS and side['value_order']==VALUES and side['tau_index']==5,'native role/slot binding')
    require(side['source']=='PEPit.wrapper.get_primal_variables (optimal_G, optimal_F)','wrapper origin')
    require(side['capture_sha256']==gram.canonical_json_sha256(c.capture)==CANONICAL_SHA,'canonical capture binding')
    require(side['numerical_convention']=='finite_decimal_strings_v1','decimal convention')
    for k in ['feasibility_checked','lean_checked','actual_lower_bound_proved','point_eval_used','projection_performed_by_exporter']:
        require(side[k] is False,'original false flag changed: '+k)
    require(len(side['gram'])==6 and all(len(r)==6 for r in side['gram']) and len(side['values'])==6,'42 native entries required')
    require(all(type(x) is str for r in side['gram'] for x in r) and all(type(x) is str for x in side['values']),'finite decimal strings required')


def read_inputs(capture,sidecar):
    _,c=archive.read_archive(capture)
    require(pipeline.digest(sidecar)==SIDECAR_SHA,'005 sidecar byte hash')
    side=gram.load_json(sidecar);validate(c,side)
    raw=Datum(tuple(tuple(Q(x) for x in r) for r in side['gram']),tuple(map(Q,side['values'])))
    return c,side,raw


def generate(raw):
    # Single bounded attempt. The input determines every coefficient independently.
    nearest=lambda x: Q(round(x*M),M)
    return Datum(tuple(tuple(nearest(x) for x in r) for r in raw.G),tuple(map(nearest,raw.F)))


def eval_expr(e,d):
    return e.const+sum(x*y for x,y in zip(e.value_coeff,d.F))+sum(e.gram_coeff[i][j]*d.G[i][j] for i in range(len(d.G)) for j in range(len(d.G)))


def conversion(c,d):
    src=c.source['base_source']['source']
    C=gram.parse_rational_matrix(src['center_matrix'],'C',5,6)
    J=gram.parse_rational_matrix(src['section_matrix'],'J',6,5)
    require(all(sum(C[i][a]*J[a][j] for a in range(6))==int(i==j) for i in range(5) for j in range(5)),'CJ != I')
    inds=c.source['base_source']['ordering']['values']['to_source']
    H=tuple(tuple(sum(C[i][a]*d.G[a][b]*C[j][b] for a in range(6) for b in range(6)) for j in range(5)) for i in range(5))
    V=tuple(d.F[i] for i in inds)
    return Datum(H,V),C,J,inds


def factor_tree(result):
    return [dict(weight=t.weight,vector=t.vector) for t in result.factors]


def audit(c,side,raw,d,nf=None):
    validate(c,side)
    require(len(d.G)==6 and all(len(r)==6 for r in d.G) and len(d.F)==6,'candidate dimensions')
    require(all(type(x) is Q for r in d.G for x in r) and all(type(x) is Q for x in d.F),'candidate must be exact rational')
    paths=[(f'gram[{i}][{j}]',raw.G[i][j],d.G[i][j]) for i in range(6) for j in range(6)]+[(f'values[{i}]',raw.F[i],d.F[i]) for i in range(6)]
    policy=[dict(path=p,raw=x,candidate=y,delta=y-x,absolute_error=abs(y-x),denominator=y.denominator,accepted=y.denominator<=M and abs(y-x)<=ETA) for p,x,y in paths]
    result=psd.synthesize_psd(d.G) if nf is None else nf
    native_psd=result.status=='psd' and psd.verify_result(d.G,result)
    rows=[eval_expr(e,d) for e in c.captured_rows]
    centered,C,J,inds=conversion(c,d)
    canonical=algebra.expected_snapshot(1)
    canonical_rows=[eval_expr(e,centered) for e in canonical.constraints]
    cf=psd.synthesize_psd(centered.G)
    beta=d.F[4]+d.F[3]-d.F[0]-d.F[1]
    objective=eval_expr(canonical.objective,centered)
    full=[None]*15
    for i,j in enumerate(c.source['coverage']['to_full']):full[j]=rows[i]
    for i in range(15):
        if full[i] is None:full[i]=Q(0) # Only original source/coverage checker authorizes these five zero rows.
    ok=all(x['accepted'] for x in policy) and native_psd and all(x<=0 for x in rows) and all(x>=0 for x in canonical_rows) and cf.status=='psd' and psd.verify_result(centered.G,cf) and d.F[5]<=beta and beta==objective and beta>0
    return dict(generation_rule=RULE,live_capture_performed=False,policy=dict(name='PRIMAL_POLICY_V1',M=M,eta=ETA,count=42,entries=policy,accepted=all(x['accepted'] for x in policy),max_error=max(policy,key=lambda e:e['absolute_error']),changed_count=sum(x!=y for _,x,y in paths),factor_denominators_checked=False),
        native_psd=native_psd,native_factor=factor_tree(result),native_rows_leZero=rows,full_rows_leZero=full,canonical_rows_geZero=canonical_rows,
        canonical_gram=centered.G,canonical_values=centered.F,canonical_factor=factor_tree(cf),C=C,J=J,CJ_identity=True,value_gather=inds,
        tau=d.F[5],beta=beta,objective=objective,candidate_diagnostic_accepted=ok)


def raw_diagnosis(c,raw):
    result=psd.synthesize_psd(raw.G)
    A=[list(r) for r in raw.G];pivots=[]
    for i in range(6):
        v=A[i][i];pivots.append(v)
        if v<=0:break
        for j in range(i+1,6):
            for k in range(i+1,6):A[j][k]-=A[j][i]*A[i][k]/v
    rows=[eval_expr(e,raw) for e in c.captured_rows]
    return dict(rows_leZero=rows,first_violated_row=next(i for i,q in enumerate(rows) if q>0),first_value=rows[0],psd_status=result.status,unpermuted_ldl_pivots=pivots,first_nonpositive_pivot=len(pivots)-1,witness=result.witness,quadratic_value=result.quadratic_value,exact_witness_verified=psd.verify_result(raw.G,result))


def factor_lean(fs):
    return '{ factors := ['+', '.join('{ weight := '+gram.lean_rat(t['weight'])+', vector := '+gram.lean_vector(t['vector'])+' }' for t in fs)+'] }'


def render(c,side,raw,d,ns):
    gram.validate_namespace(ns)
    a=audit(c,side,raw,d);require(a['candidate_diagnostic_accepted'],'candidate rejected')
    text=cap.render_module(c,ns).replace('import '+cap.AS,'import '+ADAPTER,1)
    text+='\nnamespace '+ns+'\nopen LeanPEP.GramPEP LeanPEP.Adapters\nopen scoped BigOperators\n'
    for name,x in [('rawPrimalQ',raw),('candidateQ',d)]:
        text+=f'def {name} : PGOnePrimal.NativeQ :=\n  {{ gram := {gram.lean_matrix(x.G)}, values := {gram.lean_vector(x.F)} }}\n'
    text+='def nativeFactorQ : PSDFactorCertQ 6 := '+factor_lean(a['native_factor'])+'\n'
    text+='def centeredFactorQ : PSDFactorCertQ 5 := '+factor_lean(a['canonical_factor'])+'\n'
    text+='def canonicalQ := PGOnePrimal.canonicalData sourceQ candidateQ\n'
    text+='def movedQ : DataQ (Fin 6) 6 := { candidateQ.data with value := fun i => candidateQ.values (traceQ.values.toSource i) }\n'
    diag=raw_diagnosis(c,raw)
    text+='def rawNegativeVector : VecExpr 6 ℚ := '+gram.lean_vector(diag['witness'])+'\n'
    checks={
      'source_check':'ProximalGradientSparse.checkSourceQ sourceQ = true',
      'trace_check':'ProximalGradientCapture.checkTraceQ sourceQ traceQ = true',
      'raw_dual_binding_check':'ProximalGradientCapture.checkRawBindingQ sourceQ traceQ rawUpperQ = true',
      'coverage_check':'ProximalGradientSparse.checkCoverageQ sourceQ = true',
      'policy_check':'PGOnePrimal.policy rawPrimalQ candidateQ = true',
      'native_psd_check':'checkPSDFactorQ candidateQ.gram nativeFactorQ = true',
      'native_rows_check':'checkAssumptionsFeasibleQ (PGOnePrimal.nativeModel traceQ) candidateQ.data = true',
      'full_rows_check':'checkAssumptionsFeasibleQ (ProximalGradientSparse.completedSourceQ sourceQ).model movedQ = true',
      'canonical_check':'checkAssumptionsFeasibleQ (LeanPEP.Profiles.ProximalGradient.modelQ 0) canonicalQ = true',
      'finite_check':'PGOnePrimal.checkFinite sourceQ traceQ candidateQ nativeFactorQ centeredFactorQ = true',
      'raw_rejected':'checkAssumptionsFeasibleQ (PGOnePrimal.nativeModel traceQ) rawPrimalQ.data = false',
      'raw_performance_value':'(traceQ.rows 0).evalQ rawPrimalQ.data = '+gram.lean_rat(diag['first_value']),
      'raw_negative_quadratic':'gramNormSq rawPrimalQ.gram rawNegativeVector < 0',
      'tau_beta':'candidateQ.values 5 ≤ PGOnePrimal.beta candidateQ',
      'beta_value':'PGOnePrimal.beta candidateQ = (1 / 4 : ℚ)',
      'tau_value':'candidateQ.values 5 = (1 / 4 : ℚ)',
      'center_section':'∀ i j : Fin 5, (∑ a, sourceQ.base.snapshot.centerMatrix i a * sourceQ.base.snapshot.sectionMatrix a j) = if i = j then 1 else 0',
      'counts':'(ProximalGradientSparse.completedSourceQ sourceQ).model.assumptions.length = 15 ∧ (LeanPEP.Profiles.ProximalGradient.modelQ 0).assumptions.length = 14 ∧ (gramIndexPairs 6).length + (List.finRange 6).length = 42',
      'sample_values_binding':'∀ i : Fin 5, canonicalQ.value i = candidateQ.values (![0, 2, 4, 1, 3] i)',
      'native_value_reindex':'∀ i : Fin 6, movedQ.value i = candidateQ.values (![5, 0, 1, 2, 3, 4] i)',
    }
    for name,statement in checks.items():text+=f'theorem {name} : {statement} := by\n  decide +kernel\n'
    text+='''
+theorem source_to_original :
+    ProximalGradientOrdering.nativeSourceQ (ProximalGradientRows.normalizedSourceQ sourceQ.base) =
+      ProximalGradientCoordinates.expectedSourceQ 0 :=
+  ProximalGradientRows.source_binding _ (by decide +kernel)
+
+theorem native_primal_checked :
+    IsGramPosSemidef (castDataQ candidateQ.data).gram ∧
+    AssumptionsFeasibleR (PGOnePrimal.nativeModel traceQ) (castDataQ candidateQ.data) := by
+  have h := PGOnePrimal.checkFinite_sound sourceQ traceQ candidateQ nativeFactorQ centeredFactorQ finite_check
+  exact ⟨h.1, h.2.1⟩
+
+theorem full_native_feasible :
+    AssumptionsFeasibleR (ProximalGradientSparse.completedSourceQ sourceQ).model (castDataQ movedQ) :=
+  assumptionsFeasibleQ_toReal _ _ ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp full_rows_check)
+
+theorem finite_primal_verified :
+    IsGramPosSemidef (castDataQ canonicalQ).gram ∧
+    AssumptionsFeasibleR (LeanPEP.Profiles.ProximalGradient.modelQ 0) (castDataQ canonicalQ) := by
+  have h := PGOnePrimal.checkFinite_sound sourceQ traceQ candidateQ nativeFactorQ centeredFactorQ finite_check
+  exact ⟨h.2.2.1, h.2.2.2.1⟩
+
+theorem objective_verified :
+    (LeanPEP.Profiles.ProximalGradient.objectiveQ 0).evalR (castDataQ canonicalQ) =
+      (PGOnePrimal.beta candidateQ : ℝ) ∧ 0 < (PGOnePrimal.beta candidateQ : ℝ) := by
+  have h := PGOnePrimal.checkFinite_sound sourceQ traceQ candidateQ nativeFactorQ centeredFactorQ finite_check
+  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
+
+theorem concrete_primal_transport (i j : Fin 5) :
+    (castDataQ canonicalQ).gram i j =
+      ∑ a, ∑ b, (sourceQ.base.snapshot.centerMatrix i a : ℝ) *
+        (candidateQ.gram a b : ℝ) * (sourceQ.base.snapshot.centerMatrix j b : ℝ) :=
+  PGOnePrimal.primal_transport sourceQ candidateQ i j
+'''.replace('\n+','\n')
    for name in [*checks,'source_to_original','native_primal_checked','full_native_feasible','finite_primal_verified','objective_verified','concrete_primal_transport']:
        text+='#print axioms '+name+'\n'
    text+='#print axioms PGOnePrimal.primal_transport\n#print axioms PGOnePrimal.checkFinite_sound\n'
    text+=f'end {ns}\n'
    return text


def axioms_ok(log,ns):
    found={}
    for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S):
        found[name]={x.strip() for x in body.split(',') if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms",log):found[name]=set()
    required=[ns+'.'+x for x in ['native_psd_check','policy_check','finite_check','native_primal_checked','finite_primal_verified','objective_verified','concrete_primal_transport']]+[ADAPTER+'.primal_transport',ADAPTER+'.checkFinite_sound']
    return all(x in found for x in required) and all(a<=pipeline.ALLOWED_AXIOMS for a in found.values()) and 'sorryAx' not in log


def run(capture,sidecar,directory,ns):
    require(not directory.exists() or not any(directory.iterdir()),'output must be new/empty')
    gram.validate_namespace(ns);c,side,raw=read_inputs(capture,sidecar)
    directory.mkdir(parents=True,exist_ok=True)
    report=dict(task_id='LP-V014B-PG1-PRIMAL-001',namespace=ns,generation_rule=RULE,live_capture_performed=False,selected_primal=None,native_primal_checked=False,finite_primal_verified=False,objective_verified=False,actual_lower_bound_proved=False,actual_tightness=False,status='started',capture_byte_sha256=pipeline.digest(capture),sidecar_byte_sha256=pipeline.digest(sidecar),capture_canonical_sha256=CANONICAL_SHA,commands=[])
    write(directory/'report.json',report)
    write(directory/'input_link.json',dict(capture=str(capture.resolve()),sidecar=str(sidecar.resolve()),capture_byte_sha256=pipeline.digest(capture),sidecar_byte_sha256=pipeline.digest(sidecar),capture_canonical_sha256=CANONICAL_SHA,wrapper_source='tools/capture_pepit_proximal_gradient.py:211',original_live_log='data/cases/pg/one-step-exact/capture.log',old_flags_unchanged=True))
    write(directory/'raw_audit.json',raw_diagnosis(c,raw))
    d=generate(raw);a=audit(c,side,raw,d)
    payload=dict(format='leanpep-pg1-native-primal-v1',generation_rule=RULE,native_gram=d.G,native_values=d.F,audit=a,source=c.source)
    write(directory/'candidate.json',payload)
    write(directory/'direct_policy.json',a['policy'])
    require(a['candidate_diagnostic_accepted'],'first microgrid candidate rejected')
    replay=directory/'PrimalReplay.lean';replay.write_text(render(c,side,raw,d,ns))
    commands=[(['lake','build',ADAPTER],'adapter_build.log'),(['lake','build','LeanPEP'],'library_build.log'),(['lake','env','lean','tests/lean/smoke/V13D13SmokeTest.lean'],'smoke.log'),(['lake','env','lean',str(replay.relative_to(ROOT))],'lean.log')]
    for command,name in commands:
        log=directory/name;rc=pipeline.invoke(command,log)
        report['commands'].append(dict(cwd=str(ROOT),argv=command,exit=rc,log=str(log.relative_to(ROOT)),log_sha256=pipeline.digest(log)))
        if rc:
            report['status']='lean_failed';write(directory/'report.json',report);return report,2
    if not axioms_ok((directory/'lean.log').read_text(),ns):
        report['status']='axiom_gate_failed';write(directory/'report.json',report);return report,2
    # This file is deliberately absent until ALL real Lean processes and axiom audits pass.
    write(directory/'selected_primal.json',payload)
    report.update(status='finite_primal_verified',selected_primal='selected_primal.json',native_primal_checked=True,finite_primal_verified=True,objective_verified=True,beta=a['beta'],tau=a['tau'],selected_sha256=pipeline.digest(directory/'selected_primal.json'),replay_sha256=pipeline.digest(replay),axioms_allowed=True)
    write(directory/'report.json',report);return report,0


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--capture',type=Path,default=ROOT/'data/cases/pg/one-step-exact/capture.json');p.add_argument('--sidecar',type=Path,default=ROOT/'data/cases/pg/one-step-exact/primal_observation.json');p.add_argument('--output',type=Path,required=True);p.add_argument('--namespace',required=True);a=p.parse_args()
    report,rc=run(a.capture,a.sidecar,a.output.resolve(),a.namespace);print(json.dumps(algebra.exact_json(report),indent=2));return rc

if __name__=='__main__':sys.exit(main())
