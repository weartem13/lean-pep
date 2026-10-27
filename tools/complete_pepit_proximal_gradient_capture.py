#!/usr/bin/env python3
"""D10: solve exact bound/multiplier equations at a FIXED D8 seed residual.

The D9 capture and raw endpoint remain immutable. The D8 entrywise candidate is
kept as a separate seed. Only bound and existing assumption weights may change;
objective, independent dual matrix, factors, references, and source are frozen.
Every resulting candidate is checked against raw's ORIGINAL D8 policy and the
unchanged D9 capture/source/certificate checks. Exact linear consistency alone
is not acceptance. Failure never triggers residual recomputation or clipping.
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
import solve_exact_linear_system as lin

AS = 'LeanPEP.Adapters.ProximalGradientCompletion'
LS = 'LeanPEP.GramPEP.RationalLinearSystem'


def flatten(e: gram.LinearExprSpec) -> tuple[Q, ...]:
    return (e.const,) + e.value_coeff + tuple(q for row in e.gram_coeff for q in row)


def coefficient_system(a: sparse.Artifact) -> lin.System:
    """Compile b-o = sum_j lambda_j * oriented_row[index_j] + <S,G>.

    Unknown0 is bound; remaining unknowns are weights in their ORIGINAL list
    order (including duplicate/zero entries). ALL ordered Gram entries occur.
    S is an independent fixed input, never derived by this compiler.
    """
    c = a.upper
    if c.interp_terms:
        raise ValueError('completion requires empty implicit interpolation; terms are not discarded')
    source = sparse.compact_snapshot(a)
    expressions = [flatten(source.constraints[t.index]) for t in c.assumption_terms]
    rhs = list(flatten(c.objective))
    offset = 1 + len(c.objective.value_coeff)
    for i, q in enumerate(q for row in c.dual_matrix for q in row):
        rhs[offset + i] += q
    A = tuple(tuple([Q(i == 0)] + [-e[i] for e in expressions]) for i in range(len(rhs)))
    return lin.System.make(1 + len(c.assumption_terms), A, rhs)


def fixed_targets(seed: gram.UpperSpec, final: gram.UpperSpec) -> dict[str, bool]:
    return dict(objective=seed.objective == final.objective,
        residual=seed.dual_matrix == final.dual_matrix,
        factors=seed.dual_factor == final.dual_factor,
        references=[t.index for t in seed.assumption_terms] == [t.index for t in final.assumption_terms],
        seed_implicit_empty=not seed.interp_terms, completed_implicit_empty=not final.interp_terms)


@dataclass(frozen=True)
class Completed:
    capture: cap.Converted
    system: lin.System
    linear: lin.Result
    artifact: sparse.Artifact | None
    report: dict[str, Any]


def complete(raw: Any, expected_steps: int | None = None) -> Completed:
    c = cap.convert(raw, expected_steps)
    if c.prepared is None:
        raise ValueError('prepared-only capture has no numerical candidate to complete')
    p = c.prepared
    a = p.reconstructed.artifact
    system = coefficient_system(a)
    seed = (a.upper.bound,) + tuple(t.weight for t in a.upper.assumption_terms)
    result = lin.solve(system, seed)
    final = None
    trace = cap.trace_diagnostic(c)
    binding = cap.raw_binding_diagnostic(c, p.raw.artifact.upper)
    seed_policy = prep.changes_diagnostic(p.policy, p.raw.artifact.upper, a.upper)
    report: dict[str, Any] = dict(format='leanpep-fixed-residual-completion-v1',
        capture_sha256=gram.canonical_json_sha256(c.capture), source_sha256=p.source_sha256,
        producer_claim=c.capture['producer'], producer_authenticated=False,
        lean_checked=False, live_capture_performed=False,
        scope='exact linear completion of bound and existing weights at fixed objective/residual',
        system_rows=len(system.rhs), system_columns=system.columns,
        linear_status=result.status, pivot_columns=list(result.pivot_columns),
        free_columns=list(result.free_columns), free_seed_values_preserved=True,
        independent_result_recheck=lin.verify_result(system, seed, result),
        trace_checks=trace, raw_binding_checks=binding, seed_policy_checks=seed_policy,
        raw_accepted=all(trace.values()) and all(binding.values()) and p.report['raw_accepted_diagnostic'],
        seed_accepted=all(trace.values()) and all(binding.values()) and p.report['reconstructed_joint_accepted_diagnostic'],
        completion_accepted=False, residual_recomputed=False, source_coefficients_changed=False,
        nearest_solution_claimed=False, guaranteed_reconstruction_claimed=False)
    if result.solution is not None:
        upper = replace(a.upper, bound=result.solution[0], assumption_terms=tuple(
            replace(t, weight=q) for t, q in zip(a.upper.assumption_terms, result.solution[1:])))
        final = replace(a, upper=upper, sha256='')
        final = replace(final, sha256=gram.canonical_json_sha256(sparse.artifact_tree(final)))
        if prep.source_tree(final) != prep.source_tree(a):
            raise ArithmeticError('completion mutated source data')
        frozen = fixed_targets(a.upper, upper)
        policy = prep.changes_diagnostic(p.policy, p.raw.artifact.upper, upper)
        diagnostic = sparse.diagnose(final)
        acceptance = (all(trace.values()) and all(binding.values()) and all(seed_policy.values())
            and all(frozen.values()) and all(policy.values()) and diagnostic['diagnostic_passed'])
        # Numerical audit compares FINAL directly to RAW, never only to seed.
        x, y, z = map(prep.numerical_coefficients, (p.raw.artifact.upper, a.upper, upper))
        report.update(fixed_target_checks=frozen, completed_policy_checks=policy,
            completed_diagnostic=diagnostic, completion_accepted=bool(acceptance),
            raw_bound=centered.exact_json(p.raw.artifact.upper.bound),
            seed_bound=centered.exact_json(a.upper.bound), completed_bound=centered.exact_json(upper.bound),
            changed_seed_entries=sum(v != w for v, w in zip(y, z)),
            max_raw_to_completed_error=centered.exact_json(max((abs(v-w) for v,w in zip(x,z)), default=Q(0))),
            numerical_entries=[dict(index=i,raw=centered.exact_json(v),seed=centered.exact_json(w),
                completed=centered.exact_json(q),raw_to_completed=centered.exact_json(q-v))
                for i,(v,w,q) in enumerate(zip(x,y,z))])
    else:
        report['failure_scope'] = ('No solution to this fixed-target coefficient system. '
            'This is not a proof that the source PEP is infeasible or that no other PSD residual works.')
    return Completed(c, system, result, final, report)


def system_tree(s: lin.System, r: lin.Result) -> dict[str, Any]:
    return centered.exact_json(dict(columns=s.columns,matrix=s.matrix,rhs=s.rhs,
        status=r.status,solution=r.solution,obstruction=r.obstruction,
        pivot_columns=r.pivot_columns,free_columns=r.free_columns))


def render_module(a: Completed, namespace: str) -> str:
    gram.validate_namespace(namespace)
    text = cap.render_module(a.capture, namespace).replace(f'import {cap.AS}', f'import {AS}', 1)
    ending = 'end ' + namespace + '\n'
    if not text.endswith(ending):
        raise ValueError('upstream capture renderer changed')
    additions = [f'def coefficientSystemQ : {LS}.SystemQ {len(a.system.rhs)} {a.system.columns} :=',
        '  { matrix := ' + gram.lean_matrix(a.system.matrix),
        '    rhs := ' + gram.lean_vector(a.system.rhs) + ' }']
    if a.artifact is not None:
        upper = prep._upper_text(a.artifact,namespace).replace('def upperQ :','def completedUpperQ :',1)
        if not upper.endswith(ending): raise ValueError('upstream upper renderer changed')
        additions += [upper[:-len(ending)],
            f'def completionVectorQ : Fin {a.system.columns} → ℚ := ' + gram.lean_vector(a.linear.solution)]
    elif a.linear.obstruction is not None:
        additions += [f'def obstructionQ : Fin {len(a.system.rhs)} → ℚ := ' + gram.lean_vector(a.linear.obstruction)]
    return text[:-len(ending)] + '\n' + '\n'.join(additions) + '\n' + ending


def render_replay(a: Completed, namespace: str) -> str:
    # Standalone file: no need to compile a separate generated data module.
    text = render_module(a,namespace).replace(f'import {AS}', 'import LeanPEP',1)
    text += f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\n'
    if a.report['completion_accepted']:
        text += f'''theorem exact_linear_solution : {LS}.checkSolutionQ coefficientSystemQ completionVectorQ = true := by
  decide +kernel
theorem completed_check : {AS}.checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
open scoped NNReal
theorem actual_upper {{E : Type*}} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {{L : ℝ≥0}} {{R : ℝ}} {{f h : E → ℝ}} {{g : E → E}} {{xStar : E}} {{x : ℕ → E}}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun {a.capture.capture['horizon']} L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x {a.capture.capture['horizon']}) + h (x {a.capture.capture['horizon']}) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (completedUpperQ.bound : ℝ) :=
  LeanPEP.ActualFunction.ProximalGradientCompletionAudit.upper_analytic sourceQ traceQ policyQ
    rawUpperQ reconstructedUpperQ completedUpperQ completed_check hf hh hL hR hmin hrun hradius
#print axioms completed_check
#print axioms actual_upper
'''
    elif a.linear.obstruction is not None:
        text += f'''theorem obstruction_check : {LS}.checkObstructionQ coefficientSystemQ obstructionQ = true := by
  decide +kernel
theorem no_solution : ¬ ∃ x, {LS}.IsSolutionQ coefficientSystemQ x :=
  {LS}.checked_obstruction coefficientSystemQ obstructionQ obstruction_check
#print axioms no_solution
'''
    else:
        text += f'''theorem completion_rejected : {AS}.checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = false := by
  decide +kernel
#print axioms completion_rejected
'''
    return text + 'end ' + namespace + '\n'


def outputs(a: Completed, directory: Path, namespace: str) -> dict[Path, str]:
    p = a.capture.prepared
    if p is None: raise ValueError('missing numeric endpoints')
    dump = lambda d: json.dumps(d,indent=2,sort_keys=True) + '\n'
    result = {directory/'capture_input.json':dump(a.capture.capture),
        directory/'source.json':dump(a.capture.source),
        directory/'raw_exact.json':dump(sparse.artifact_tree(p.raw.artifact)),
        directory/'seed_exact.json':dump(sparse.artifact_tree(p.reconstructed.artifact)),
        directory/'linear_system.json':dump(system_tree(a.system,a.linear)),
        directory/'completion_report.json':dump(a.report),
        directory/'Completion.lean':render_module(a,namespace),
        directory/'Replay.lean':render_replay(a,namespace)}
    if a.artifact is not None:
        result[directory/'completed_exact.json'] = dump(sparse.artifact_tree(a.artifact))
    return result


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--expected-steps',type=int)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--namespace',required=True)
    ap.add_argument('--require-completed-pass',action='store_true')
    args=ap.parse_args(argv)
    try:
        a = complete(gram.load_json(args.input),args.expected_steps)
        out = outputs(a,args.output_dir,args.namespace)
        if any(p.resolve()==args.input.resolve() for p in out):
            raise ValueError('output would overwrite the original capture')
        if args.output_dir.exists() and any(args.output_dir.iterdir()):
            raise ValueError('output directory must be empty; refusing stale candidate artifacts')
        for path,text in out.items(): gram.atomic_write(path,text)
        print(json.dumps(dict(linear_status=a.linear.status,seed_accepted=a.report['seed_accepted'],
            completion_accepted=a.report['completion_accepted'],lean_checked=False,
            live_capture_performed=False)))
        return 2 if args.require_completed_pass and not a.report['completion_accepted'] else 0
    except (ValueError,ArithmeticError,OSError) as exc:
        print('error: '+str(exc),file=sys.stderr)
        return 1

if __name__ == '__main__': raise SystemExit(main())
