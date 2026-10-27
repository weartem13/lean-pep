#!/usr/bin/env python3
"""Untrusted, archive-specific PG T=2 affine-grid candidate and original replay.

Solve only the constant/value source equations, using bounded exact grid seeds
from the current raw multipliers. Form a NEW residual from all source Gram
coefficients; use the unchanged D1 factor producer and original D9 checker.
No solver, PSD projection, T=1 formula, or known rate is used by this generator.
"""
from __future__ import annotations
import argparse
from dataclasses import replace
from fractions import Fraction as Q
import hashlib
from pathlib import Path
import traceback

import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep
import run_pepit_pipeline as pipeline
import solve_exact_linear_system as linear
import synthesize_psd_factors as psd

CAPTURE_SHA256 = '17141488ec3453e8b8d81196d973a01a9bae831a1baa88bd6a96e8ea8b2297b7'
GENERATION_RULE = 'pg_t2_source_affine_common_grid_v1'
BASIS = ['x_star', 'g_star', 'x0', 'g0', 's1', 'g1', 's2', 'g2']
LABELS = [('performance',), ('radius', None, None)] + [
    ('smoothPair', i, j) for i in range(4) for j in range(4) if i != j
] + [('convexPair', i, j) for i in range(3) for j in range(3) if i != j]
MAX_GRID_TRIALS = 64


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rational(q):
    return dict(num=q.numerator, den=q.denominator)


def validate_source(c):
    require(c.prepared is not None, 'numerical capture required')
    require(c.capture['horizon'] == 2 and c.capture['basis_order'] == BASIS, 'T=2/native basis mismatch')
    require(c.prepared.policy.max_denominator == 1000000 and
            c.prepared.policy.max_abs_error == Q(1, 1000000), 'original M/eta required')
    require(prep._policy(c.capture['policy']) == c.prepared.policy, 'capture/parsed policy mismatch')
    require([cap.label_key(row['label']) for row in c.capture['constraints']] == LABELS,
            'source row labels/order mismatch')
    require(c.source_passed and all(cap.trace_diagnostic(c).values()), 'original source/trace rejected')
    raw = c.prepared.raw.artifact.upper
    require(all(cap.raw_binding_diagnostic(c, raw).values()), 'raw binding rejected')
    require(not raw.interp_terms and [t.index for t in raw.assumption_terms] == list(range(20)),
            'ordered references mismatch')


def read_archive(path):
    original = path.read_bytes()
    require(hashlib.sha256(original).hexdigest() == CAPTURE_SHA256, 'PG2 archive byte hash mismatch')
    c = cap.convert(gram.load_json(path), 2)
    validate_source(c)
    return original, c


def value_system(a):
    o, rows = a.upper.objective, a.compact_rows
    matrix = [[Q(1)] + [e.const for e in rows]]
    matrix += [[Q(0)] + [e.value_coeff[j] for e in rows] for j in range(len(o.value_coeff))]
    return linear.System.make(1+len(rows), matrix, [o.const, *o.value_coeff])


def grid_seed(value, denominator, upward=False):
    n, d = value.numerator * denominator, value.denominator
    return Q(-(-n // d) if upward else (2*n+d)//(2*d), denominator)


def audit_candidate(c, candidate):
    validate_source(c)
    p = c.prepared
    raw = p.raw.artifact
    require(prep.source_tree(candidate) == prep.source_tree(raw), 'candidate source differs')
    xs, ys = prep.numerical_coefficients(raw.upper), prep.numerical_coefficients(candidate.upper)
    require(len(xs) == len(ys) == len(p.entries) == 158, 'policy coefficient count mismatch')
    require(xs == tuple(e.raw for e in p.entries), 'policy traversal mismatch')
    changes = prep.changes_diagnostic(p.policy, raw.upper, candidate.upper)
    entries = [dict(path=e.path, raw=rational(x), candidate=rational(y), delta=rational(y-x),
                    absolute_error=rational(abs(y-x)), within_error=abs(y-x)<=p.policy.max_abs_error,
                    denominator_within_policy=y.denominator<=p.policy.max_denominator)
               for e,x,y in zip(p.entries,xs,ys)]
    i = max(range(len(xs)), key=lambda j: abs(ys[j]-xs[j]))
    diagnostic = sparse.diagnose(candidate)
    return dict(original_policy=c.capture['policy'], policy_checks=changes, coefficient_count=len(xs),
        changed_count=sum(x!=y for x,y in zip(xs,ys)), entries=entries,
        max_abs_error=rational(abs(ys[i]-xs[i])), max_abs_error_path=entries[i]['path'],
        max_candidate_coefficient_denominator=max(y.denominator for y in ys),
        factor_denominators_subject_to_policy=False, source_unchanged=True,
        trace_checks=cap.trace_diagnostic(c,candidate), raw_binding_checks=cap.raw_binding_diagnostic(c,raw.upper),
        structured_diagnostic=diagnostic,
        candidate_diagnostic_accepted=all(changes.values()) and diagnostic['diagnostic_passed'] and
            all(cap.trace_diagnostic(c,candidate).values()), lean_checked=False)


def build_candidate(c):
    validate_source(c)
    raw = c.prepared.raw.artifact
    system = value_system(raw)
    start = (raw.upper.bound,) + tuple(t.weight for t in raw.upper.assumption_terms)
    trials = []
    for D in range(500000, 500000-MAX_GRID_TRIALS, -1):
        # Unknown 2 is the radius multiplier; the exact constant equation ties
        # it to the bound. All other free seeds use exact nearest-grid rounding.
        seed = tuple(grid_seed(v,D,upward=(j==2)) for j,v in enumerate(start))
        result = linear.solve(system,seed)
        require(result.status == 'solution', 'source constant/value system inconsistent')
        b, *weights = result.solution
        require(len(weights)==len(raw.compact_rows)==len(raw.upper.assumption_terms)==20, 'row length mismatch')
        S = tuple(tuple(-raw.upper.objective.gram_coeff[i][j] +
            sum(w*e.gram_coeff[i][j] for w,e in zip(weights,raw.compact_rows))
            for j in range(8)) for i in range(8))
        upper = replace(raw.upper,bound=b,assumption_terms=tuple(
            replace(t,weight=w) for t,w in zip(raw.upper.assumption_terms,weights)),
            dual_matrix=S,dual_factor=gram.FactorCertSpec(()))
        guards = prep.changes_diagnostic(c.prepared.policy,raw.upper,upper)
        trial = dict(denominator=D,policy_checks=guards,nonnegative_weights=all(w>=0 for w in weights))
        trials.append(trial)
        if not all(guards.values()) or not trial['nonnegative_weights']:
            continue
        factor = psd.synthesize_psd(S)
        require(psd.verify_result(S,factor), 'D1 output failed exact recheck')
        trial['psd'] = psd.result_report(S,factor)
        if factor.status != 'psd':
            continue
        upper = replace(upper,dual_factor=gram.FactorCertSpec(tuple(
            gram.RankOneFactorSpec(t.weight,t.vector) for t in factor.factors)))
        candidate = sparse.parse_artifact(sparse.artifact_tree(replace(raw,upper=upper)),2)
        audit = audit_candidate(c,candidate)
        trial['original_upper_accepted'] = audit['candidate_diagnostic_accepted']
        if audit['candidate_diagnostic_accepted']:
            generation = dict(generation_rule=GENERATION_RULE,residual_recomputed=True,
                denominator=D,max_grid_trials=MAX_GRID_TRIALS,trial_count=len(trials),trials=trials,
                free_indices=list(result.free_columns),pivot_indices=list(result.pivot_columns),
                system=dict(matrix=[[rational(q) for q in row] for row in system.matrix],
                            rhs=[rational(q) for q in system.rhs]),
                constant_value_solution=[rational(q) for q in result.solution],
                raw_seed=[rational(q) for q in start],grid_seed=[rational(q) for q in seed],
                bound=rational(b),factor_count=len(factor.factors),known_rate_used=False)
            return candidate,audit,generation
    raise ValueError('bounded grid search exhausted; no infeasibility claim')


def render_replay(c,candidate,namespace):
    gram.validate_namespace(namespace)
    require(audit_candidate(c,candidate)['candidate_diagnostic_accepted'],'structured candidate rejected')
    text = cap.render_module(c,namespace).replace('import '+cap.AS,'import LeanPEP',1)
    text += f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\n'
    text += prep._upper_text(candidate,namespace).replace('def upperQ :','def structuredUpperQ :',1)
    text += f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\nopen scoped NNReal\n'
    checks = dict(source_check='LeanPEP.Adapters.ProximalGradientSparse.checkSourceQ sourceQ',
        trace_check=f'{cap.AS}.checkTraceQ sourceQ traceQ',
        raw_binding_check=f'{cap.AS}.checkRawBindingQ sourceQ traceQ rawUpperQ',
        policy_check='RationalReconstructionAudit.checkChangesQ policyQ rawUpperQ structuredUpperQ',
        psd_check='checkPSDFactorQ structuredUpperQ.dualMatrix structuredUpperQ.dualFactor',
        upper_check='checkUpperCertQ structuredUpperQ',
        structured_check=f'{cap.AS}.checkCapturedQ sourceQ traceQ policyQ rawUpperQ structuredUpperQ')
    for name,expr in checks.items():
        text += f'theorem {name} : {expr} = true := by\n  decide +kernel\n'
    text += f'theorem structured_bound : structuredUpperQ.bound = {gram.lean_rat(candidate.upper.bound)} := by\n  decide +kernel\n'
    text += '''theorem policy_count : (RationalReconstructionAudit.numericalCoefficientsQ structuredUpperQ).length = 158 := by
  decide +kernel

theorem actual_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun 2 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 2) + h (x 2) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (structuredUpperQ.bound : ℝ) :=
  LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic
    sourceQ traceQ policyQ rawUpperQ structuredUpperQ structured_check
    hf hh hL hR hmin hrun hradius
'''
    for name in (*checks,'structured_bound','policy_count','actual_upper'):
        text += f'#print axioms {name}\n'
    return text+f'end {namespace}\n'


def run(input_path,directory,namespace):
    gram.validate_namespace(namespace)
    require(not directory.exists() or directory.is_dir() and not any(directory.iterdir()),'output directory must be new or empty')
    original,c = read_archive(input_path)
    directory.mkdir(parents=True,exist_ok=True)
    (directory/'capture.json').write_bytes(original)
    report = dict(format='leanpep-structured-pg-two-v1',mode='archive_structured',horizon=2,
        generation_rule=GENERATION_RULE,residual_recomputed=True,capture_bytes_sha256=CAPTURE_SHA256,
        selected_endpoint=None,candidate_accepted=False,actual_upper_verified=False,
        live_capture_performed=False,d13_acceptance_met=False,primal_certified=False,tightness_claimed=False,
        source_coefficients_changed=False,raw_modified=False,namespace=namespace,status='started')
    try:
        candidate,audit,generation=build_candidate(c)
        for name,data in [('direct_audit',audit),('generation',generation),
                          ('raw_exact',sparse.artifact_tree(c.prepared.raw.artifact)),
                          ('candidate_exact',sparse.artifact_tree(candidate))]:
            pipeline.write_json(directory/(name+'.json'),data)
        replay=directory/'Replay.lean'
        gram.atomic_write(replay,render_replay(c,candidate,namespace))
        report['candidate_bytes_sha256']=pipeline.digest(directory/'candidate_exact.json')
        report['replay_bytes_sha256']=pipeline.digest(replay)
        report['lean']=pipeline.check_lean(replay,directory,namespace,True)
        if report['lean']['checked']:
            (directory/'selected_exact.json').write_bytes((directory/'candidate_exact.json').read_bytes())
            report.update(candidate_accepted=True,actual_upper_verified=True,selected_endpoint='structured',
                          bound=rational(candidate.upper.bound),status='verified_upper')
        else:
            report['status']='lean_failed_or_unavailable'
        report['interface_smoke_exit']=pipeline.invoke(['lake','env','lean','tests/lean/smoke/V13D13SmokeTest.lean'],directory/'interface_smoke.log')
        return report,0 if report['actual_upper_verified'] and report['interface_smoke_exit']==0 else 3
    except Exception as exc:
        report.update(status='failed',error=f'{type(exc).__name__}: {exc}')
        (directory/'error.log').write_text(traceback.format_exc())
        return report,1
    finally:
        report['input_bytes_unchanged']=input_path.read_bytes()==original
        pipeline.write_json(directory/'structured_report.json',report)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--namespace',required=True)
    args=parser.parse_args()
    try:
        report,code=run(args.input,args.output_dir,args.namespace)
        print(pipeline.dump(report));return code
    except (ValueError,OSError) as exc:
        parser.exit(1,f'error: {exc}\n')

if __name__=='__main__':
    raise SystemExit(main())
