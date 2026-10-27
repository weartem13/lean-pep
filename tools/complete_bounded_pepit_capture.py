#!/usr/bin/env python3
"""D11: nonnegative, raw-budget-constrained completion at a fixed seed residual.

The OLD D10 coefficient compiler and OLD D9/D8/D7 checks remain authoritative.
An exact phase-I search may move free variables; bound is not forced positive.
The box enforces raw +/- eta, and multiplier lower bounds also include zero.
Denominator limits are NOT linear constraints; they are rechecked afterwards.
A feasible rational box point may still fail the final certificate/policy audit.
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
import import_proximal_gradient_sparse as sparse
import import_pepit_proximal_gradient_capture as cap
import prepare_proximal_gradient_candidates as prep
import complete_pepit_proximal_gradient_capture as old
import solve_exact_linear_system as lin
import solve_exact_box_system as box

BS='LeanPEP.GramPEP.RationalBoxSystem'

@dataclass(frozen=True)
class Completed:
    previous: old.Completed
    box: box.BoxSystem
    result: box.Result
    artifact: sparse.Artifact | None
    report: dict[str,Any]


def raw_bounds(raw: gram.UpperSpec, eta: Q) -> tuple[tuple[Q,...],tuple[Q,...]]:
    if eta < 0: raise ValueError('negative error budget')
    values=(raw.bound,)+tuple(t.weight for t in raw.assumption_terms)
    return (tuple(v-eta if j==0 else max(Q(0),v-eta) for j,v in enumerate(values)),
            tuple(v+eta for v in values))


def complete(data: Any, expected_steps: int | None=None, *, max_pivots: int=10000) -> Completed:
    # Keep the old free-seed attempt as a separate endpoint; never overwrite it.
    previous=old.complete(data,expected_steps)
    p=previous.capture.prepared
    assert p is not None
    seed=p.reconstructed.artifact
    lo,hi=raw_bounds(p.raw.artifact.upper,p.policy.max_abs_error)
    problem=box.BoxSystem.make(previous.system,lo,hi)
    start=previous.linear.solution
    if start is None:
        start=(seed.upper.bound,)+tuple(t.weight for t in seed.upper.assumption_terms)
    result=box.solve(problem,start,max_pivots=max_pivots)
    if not box.verify_result(problem,result):
        raise ArithmeticError('bounded solver result failed original-system recheck')
    report=dict(format='leanpep-bounded-completion-v1',
        capture_sha256=gram.canonical_json_sha256(previous.capture.capture),
        source_sha256=p.source_sha256,producer_claim=previous.capture.capture['producer'],
        producer_authenticated=False,live_capture_performed=False,lean_checked=False,
        solver='exact_phase_I_least_index',box_status=result.status,pivots=result.pivots,
        max_pivots=max_pivots,seed_used=result.seed_used,
        system_rows=len(previous.system.rhs),system_columns=previous.system.columns,
        independent_box_recheck=box.verify_result(problem,result),
        d10_linear_status=previous.linear.status,d10_completion_accepted=previous.report['completion_accepted'],
        d10_free_columns=list(previous.linear.free_columns),
        raw_accepted=previous.report['raw_accepted'],seed_accepted=previous.report['seed_accepted'],
        completion_accepted=False,box_based_on='raw_not_seed',
        residual_recomputed=False,source_coefficients_changed=False,
        denominator_constraint_searched=False,nearest_solution_claimed=False,
        optimal_bound_claimed=False,free_seed_values_required=False)
    final=None
    if result.solution is not None:
        if len(result.solution)!=1+len(seed.upper.assumption_terms):
            raise ArithmeticError('solution/reference length mismatch')
        upper=replace(seed.upper,bound=result.solution[0],assumption_terms=tuple(
            replace(t,weight=q) for t,q in zip(seed.upper.assumption_terms,result.solution[1:])))
        final=replace(seed,upper=upper,sha256='')
        final=replace(final,sha256=gram.canonical_json_sha256(sparse.artifact_tree(final)))
        if prep.source_tree(final)!=prep.source_tree(seed):
            raise ArithmeticError('bounded completion changed the source')
        trace=cap.trace_diagnostic(previous.capture)
        binding=cap.raw_binding_diagnostic(previous.capture,p.raw.artifact.upper)
        seed_policy=prep.changes_diagnostic(p.policy,p.raw.artifact.upper,seed.upper)
        policy=prep.changes_diagnostic(p.policy,p.raw.artifact.upper,upper)
        fixed=old.fixed_targets(seed.upper,upper)
        diag=sparse.diagnose(final)
        accepted=all(trace.values()) and all(binding.values()) and all(seed_policy.values()) and all(policy.values()) and all(fixed.values()) and diag['diagnostic_passed']
        x,y,z=map(prep.numerical_coefficients,(p.raw.artifact.upper,seed.upper,upper))
        report.update(trace_checks=trace,raw_binding_checks=binding,seed_policy_checks=seed_policy,
            completed_policy_checks=policy,fixed_target_checks=fixed,completed_diagnostic=diag,
            completion_accepted=bool(accepted),completed_bound=centered.exact_json(upper.bound),
            changed_seed_entries=sum(a!=b for a,b in zip(y,z)),
            moved_d10_free_columns=[j for j in previous.linear.free_columns
                if previous.linear.solution is not None and result.solution[j]!=previous.linear.solution[j]],
            max_raw_to_completed_error=centered.exact_json(max((abs(a-b) for a,b in zip(x,z)),default=Q(0))))
    elif result.obstruction is not None:
        report.update(obstruction_margin=centered.exact_json(box.obstruction_value(problem,result.obstruction)),
            failure_scope='No rational point in THIS submitted coefficient system and raw budget/nonnegativity box. '
              'The source-to-system compiler is not formally verified here. This is not general PEP infeasibility, '
              'not absence of a certificate with a different residual, and not a denominator-search claim.')
    else:
        report['failure_scope']='Pivot limit reached: no feasibility or infeasibility conclusion.'
    return Completed(previous,problem,result,final,report)


def box_tree(a: Completed) -> dict[str,Any]:
    s,w=a.box,a.result.obstruction
    return centered.exact_json(dict(matrix=s.system.matrix,rhs=s.system.rhs,columns=s.system.columns,
        lower=s.lower,upper=s.upper,status=a.result.status,solution=a.result.solution,
        obstruction=None if w is None else dict(equality=w.equality,lower=w.lower,upper=w.upper)))


def render_module(a: Completed, namespace: str) -> str:
    gram.validate_namespace(namespace)
    capture=a.previous.capture
    text=cap.render_module(capture,namespace).replace(f'import {cap.AS}',f'import {old.AS}\nimport {BS}',1)
    ending='end '+namespace+'\n'
    if not text.endswith(ending): raise ValueError('upstream renderer changed')
    s=a.box.system;p=capture.prepared
    assert p is not None
    raw=(p.raw.artifact.upper.bound,)+tuple(t.weight for t in p.raw.artifact.upper.assumption_terms)
    parts=[f'def coefficientSystemQ : {old.LS}.SystemQ {len(s.rhs)} {s.columns} :=',
        '  { matrix := '+gram.lean_matrix(s.matrix), '    rhs := '+gram.lean_vector(s.rhs)+' }',
        f'def rawVectorQ : Fin {s.columns} → ℚ := '+gram.lean_vector(raw),
        f'def signMaskQ : Fin {s.columns} → Bool := fun j => decide (j.val ≠ 0)',
        f'def boxQ : {BS}.BoxQ {len(s.rhs)} {s.columns} :=',
        '  { system := coefficientSystemQ', '    lower := '+gram.lean_vector(a.box.lower),
        '    upper := '+gram.lean_vector(a.box.upper)+' }']
    if a.previous.artifact is not None:
        oldtext=prep._upper_text(a.previous.artifact,namespace).replace('def upperQ :','def freeSeedUpperQ :',1)
        parts.append(oldtext[:-len(ending)])
        parts.append(f'def freeSeedVectorQ : Fin {s.columns} → ℚ := '+gram.lean_vector(a.previous.linear.solution))
    if a.artifact is not None:
        parts.append(prep._upper_text(a.artifact,namespace).replace('def upperQ :','def completedUpperQ :',1)[:-len(ending)])
        parts.append(f'def completionVectorQ : Fin {s.columns} → ℚ := '+gram.lean_vector(a.result.solution))
    if a.result.obstruction is not None:
        w=a.result.obstruction
        parts += [f'def boxObstructionQ : {BS}.ObstructionQ {len(s.rhs)} {s.columns} :=',
                  '  { equality := '+gram.lean_vector(w.equality),
                  '    lower := '+gram.lean_vector(w.lower),
                  '    upper := '+gram.lean_vector(w.upper)+' }']
    return text[:-len(ending)]+'\n'+'\n'.join(parts)+'\n'+ending


def render_replay(a: Completed, namespace: str) -> str:
    text=render_module(a,namespace).replace(f'import {old.AS}\nimport {BS}','import LeanPEP',1)
    text+=f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\n'
    text+=f'''theorem raw_vector_check : List.ofFn rawVectorQ =
    rawUpperQ.bound :: rawUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem box_bounds_check :
    boxQ.lower = {BS}.policyLowerQ rawVectorQ policyQ.maxAbsError signMaskQ ∧
    boxQ.upper = {BS}.policyUpperQ rawVectorQ policyQ.maxAbsError := by
  decide +kernel
'''
    if a.result.solution is not None:
        text+=f'''theorem completion_vector_check : List.ofFn completionVectorQ =
    completedUpperQ.bound :: completedUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem box_feasible_check : {BS}.checkFeasibleQ boxQ completionVectorQ = true := by
  decide +kernel
'''
    if a.report['completion_accepted']:
        T=a.previous.capture.capture['horizon']
        text+=f'''theorem completed_check : {old.AS}.checkCompletedQ sourceQ traceQ policyQ
    rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
open scoped NNReal
theorem actual_upper {{E : Type*}} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {{L : ℝ≥0}} {{R : ℝ}} {{f h : E → ℝ}} {{g : E → E}} {{xStar : E}} {{x : ℕ → E}}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun {T} L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x {T}) + h (x {T}) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (completedUpperQ.bound : ℝ) :=
  LeanPEP.ActualFunction.ProximalGradientCompletionAudit.upper_analytic sourceQ traceQ policyQ
    rawUpperQ reconstructedUpperQ completedUpperQ completed_check hf hh hL hR hmin hrun hradius
#print axioms completed_check
#print axioms actual_upper
'''
    if a.result.obstruction is not None:
        text+=f'''theorem box_obstruction_check : {BS}.checkObstructionQ boxQ boxObstructionQ = true := by
  decide +kernel
theorem no_box_solution : ¬ ∃ x, {BS}.FeasibleQ boxQ x :=
  {BS}.checked_obstruction boxQ boxObstructionQ box_obstruction_check
#print axioms no_box_solution
'''
    return text+'end '+namespace+'\n'


def outputs(a: Completed,directory: Path,namespace: str) -> dict[Path,str]:
    p=a.previous.capture.prepared
    assert p is not None
    dump=lambda v:json.dumps(v,indent=2,sort_keys=True)+'\n'
    out={directory/'capture_input.json':dump(a.previous.capture.capture),
         directory/'source.json':dump(a.previous.capture.source),
         directory/'raw_exact.json':dump(sparse.artifact_tree(p.raw.artifact)),
         directory/'seed_exact.json':dump(sparse.artifact_tree(p.reconstructed.artifact)),
         directory/'box_system.json':dump(box_tree(a)),
         directory/'bounded_report.json':dump(a.report),
         directory/'free_seed_report.json':dump(a.previous.report),
         directory/'BoundedCompletion.lean':render_module(a,namespace),
         directory/'Replay.lean':render_replay(a,namespace)}
    if a.previous.artifact is not None:
        out[directory/'free_seed_exact.json']=dump(sparse.artifact_tree(a.previous.artifact))
    if a.artifact is not None:
        out[directory/'completed_exact.json']=dump(sparse.artifact_tree(a.artifact))
    return out


def main(argv: list[str] | None=None) -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('--expected-steps',type=int)
    parser.add_argument('--max-pivots',type=int,default=10000)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--namespace',required=True)
    parser.add_argument('--require-completed-pass',action='store_true')
    args=parser.parse_args(argv)
    try:
        if args.output_dir.exists() and any(args.output_dir.iterdir()):
            raise ValueError('output directory must be empty; refusing stale candidate artifacts')
        a=complete(gram.load_json(args.input),args.expected_steps,max_pivots=args.max_pivots)
        out=outputs(a,args.output_dir,args.namespace)
        if any(p.resolve()==args.input.resolve() for p in out):
            raise ValueError('output would overwrite the input capture')
        for p,t in out.items(): gram.atomic_write(p,t)
        print(json.dumps(dict(box_status=a.result.status,pivots=a.result.pivots,
            d10_completion_accepted=a.previous.report['completion_accepted'],
            completion_accepted=a.report['completion_accepted'],lean_checked=False)))
        return 2 if args.require_completed_pass and not a.report['completion_accepted'] else 0
    except (ValueError,ArithmeticError,OSError) as exc:
        print('error: '+str(exc),file=sys.stderr);return 1

if __name__=='__main__':raise SystemExit(main())
