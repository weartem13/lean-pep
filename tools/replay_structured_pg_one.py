#!/usr/bin/env python3
"""Archive-specific, untrusted structured T=1 candidate and original D9 replay.

No live solver, no modification of raw or the old reconstructed endpoint, and
no change to D10/D11's fixed-residual completion contract. This entry deliberately
supports only the reviewed 005 archive. selected_exact is written only after
actual execution of the original Lean checker and actual-function theorem.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import traceback

import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep
import run_pepit_pipeline as pipeline

CAPTURE_SHA256 = '69ab11490086c9d6e704b6b6693d45e783a84ed61fe1c14519e423c4a608250b'
GENERATION_RULE = 'pg_t1_source_affine_rank3_v1'
BASIS = ['x_star', 'g_star', 'x0', 'g0', 's1', 'g1']
LABELS = [('performance',), ('radius', None, None)] + [
    ('smoothPair', i, j) for i, j in ((0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1))
] + [('convexPair', 0, 1), ('convexPair', 1, 0)]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rational(q: Q) -> dict:
    return dict(num=q.numerator, den=q.denominator)


def read_archive(path: Path) -> tuple[bytes, cap.Converted]:
    original = path.read_bytes()
    require(hashlib.sha256(original).hexdigest() == CAPTURE_SHA256, '005 capture byte hash mismatch')
    c = cap.convert(gram.load_json(path), 1)
    validate_source(c)
    return original, c


def validate_source(c: cap.Converted) -> None:
    require(c.prepared is not None, 'numerical capture required')
    d = c.capture
    require(d['horizon'] == 1 and d['basis_order'] == BASIS, 'unexpected T/native basis')
    require(d['policy']['max_denominator'] == 1000000 and
            prep.decimal(d['policy']['max_abs_error'], 'eta')[1] == Q(1, 1000000), 'original policy required')
    require(c.prepared.policy.max_denominator == 1000000 and
            c.prepared.policy.max_abs_error == Q(1, 1000000), 'parsed policy mismatch')
    require([cap.label_key(row['label']) for row in d['constraints']] == LABELS,
            'source row labels/order mismatch')
    require(all(row['sense'] == 'leZero' for row in d['constraints']), 'row sense mismatch')
    require(c.source_passed and all(cap.trace_diagnostic(c).values()), 'original source/trace rejected')
    raw = c.prepared.raw.artifact.upper
    require(all(cap.raw_binding_diagnostic(c, raw).values()), 'original raw binding rejected')
    require(not raw.interp_terms and [t.index for t in raw.assumption_terms] == list(range(10)),
            'original ordered references mismatch')


def build_candidate(c: cap.Converted) -> sparse.Artifact:
    validate_source(c)
    raw = c.prepared.raw.artifact
    M = c.prepared.policy.max_denominator
    b = prep.decimal(c.capture['numerical']['bound'], 'bound')[1].limit_denominator(M)
    a = prep.decimal(c.capture['numerical']['multipliers'][2], 'weight[2]')[1].limit_denominator(M // 2)
    require(b == Q(1, 4) and 0 < a <= Q(1, 2), 'outside the reviewed rank-three family')
    weights = (Q(1), b, a, 1-a, Q(0), 1-a, Q(0), 1-2*a, Q(1), Q(0))
    rows = raw.compact_rows
    o = raw.upper.objective
    # All source rows are leZero with scale=1: b-o = -sum(lambda*q) + <S,G>.
    constant = b - o.const + sum(w * e.const for w, e in zip(weights, rows))
    values = tuple(-o.value_coeff[j] + sum(w * e.value_coeff[j] for w, e in zip(weights, rows))
                   for j in range(len(o.value_coeff)))
    require(constant == 0 and all(v == 0 for v in values), 'constant/value identity mismatch')
    S = tuple(tuple(-o.gram_coeff[i][j] + sum(w * e.gram_coeff[i][j] for w, e in zip(weights, rows))
                    for j in range(6)) for i in range(6))
    factors = gram.FactorCertSpec((
        gram.RankOneFactorSpec(Q(1, 4), (Q(1), Q(0), Q(-1), 2*a, Q(2), 2-2*a)),
        gram.RankOneFactorSpec(Q(1, 2), (Q(0), Q(1), Q(0), -a, Q(0), a-1)),
        gram.RankOneFactorSpec(a*(2-3*a)/2, (Q(0), Q(0), Q(0), Q(1), Q(0), Q(-1))),
    ))
    upper = replace(raw.upper, bound=b, assumption_terms=tuple(
        replace(t, weight=w) for t, w in zip(raw.upper.assumption_terms, weights)),
        dual_matrix=S, dual_factor=factors)
    # Round-trip through the unchanged exact parser, including source and factors.
    return sparse.parse_artifact(sparse.artifact_tree(replace(raw, upper=upper)), 1)


def audit_candidate(c: cap.Converted, candidate: sparse.Artifact) -> dict:
    validate_source(c)
    p = c.prepared
    raw = p.raw.artifact
    require(prep.source_tree(candidate) == prep.source_tree(raw), 'candidate source differs from raw source')
    changes = prep.changes_diagnostic(p.policy, raw.upper, candidate.upper)
    diagnostic = sparse.diagnose(candidate)
    xs = prep.numerical_coefficients(raw.upper)
    ys = prep.numerical_coefficients(candidate.upper)
    require(len(xs) == len(ys) == len(p.entries) == 90, 'policy coefficient count mismatch')
    require(xs == tuple(e.raw for e in p.entries), 'policy traversal mismatch')
    entries = [dict(path=e.path, raw=rational(x), candidate=rational(y), delta=rational(y-x),
                    absolute_error=rational(abs(y-x)), within_error=abs(y-x) <= p.policy.max_abs_error,
                    denominator_within_policy=y.denominator <= p.policy.max_denominator)
               for e, x, y in zip(p.entries, xs, ys)]
    index = max(range(len(xs)), key=lambda i: abs(ys[i]-xs[i]))
    return dict(generation_rule=GENERATION_RULE, selected_endpoint='structured', residual_recomputed=True,
        source_unchanged=True, trace_checks=cap.trace_diagnostic(c, candidate),
        raw_binding_checks=cap.raw_binding_diagnostic(c, raw.upper),
        policy=changes, original_policy=c.capture['policy'], coefficient_count=len(xs),
        changed_count=sum(x != y for x, y in zip(xs, ys)), entries=entries,
        max_abs_error=rational(abs(ys[index]-xs[index])), max_abs_error_path=entries[index]['path'],
        max_candidate_coefficient_denominator=max(y.denominator for y in ys),
        factor_denominators_subject_to_policy=False, factor_policy_basis='RationalReconstructionAudit.numericalCoefficientsQ',
        structured_diagnostic=diagnostic,
        candidate_diagnostic_accepted=all(changes.values()) and diagnostic['diagnostic_passed'] and
            all(cap.trace_diagnostic(c, candidate).values()),
        lean_checked=False, live_capture_performed=False)


def render_replay(c: cap.Converted, candidate: sparse.Artifact, namespace: str) -> str:
    gram.validate_namespace(namespace)
    require(audit_candidate(c, candidate)['candidate_diagnostic_accepted'], 'structured candidate rejected')
    # Preserve all literal source/raw/trace/old reconstructed data. Append a
    # separately named endpoint; never substitute it for reconstructedUpperQ.
    text = cap.render_module(c, namespace).replace('import ' + cap.AS, 'import LeanPEP', 1)
    text += f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\n'
    text += prep._upper_text(candidate, namespace).replace('def upperQ :', 'def structuredUpperQ :', 1)
    text += f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\nopen scoped NNReal\n'
    checks = {
        'source_check': 'LeanPEP.Adapters.ProximalGradientSparse.checkSourceQ sourceQ',
        'trace_check': f'{cap.AS}.checkTraceQ sourceQ traceQ',
        'raw_binding_check': f'{cap.AS}.checkRawBindingQ sourceQ traceQ rawUpperQ',
        'policy_check': 'RationalReconstructionAudit.checkChangesQ policyQ rawUpperQ structuredUpperQ',
        'psd_check': 'checkPSDFactorQ structuredUpperQ.dualMatrix structuredUpperQ.dualFactor',
        'upper_check': 'checkUpperCertQ structuredUpperQ',
        'structured_check': f'{cap.AS}.checkCapturedQ sourceQ traceQ policyQ rawUpperQ structuredUpperQ',
    }
    for name, expression in checks.items():
        text += f'theorem {name} : {expression} = true := by\n  decide +kernel\n'
    text += '''theorem structured_bound : structuredUpperQ.bound = (1 / 4 : ℚ) := by
  decide +kernel
theorem policy_count : (RationalReconstructionAudit.numericalCoefficientsQ structuredUpperQ).length = 90 := by
  decide +kernel

theorem actual_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun 1 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 1) + h (x 1) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (structuredUpperQ.bound : ℝ) :=
  LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic
    sourceQ traceQ policyQ rawUpperQ structuredUpperQ structured_check
    hf hh hL hR hmin hrun hradius
'''
    for name in (*checks, 'structured_bound', 'policy_count', 'actual_upper'):
        text += f'#print axioms {name}\n'
    return text + f'end {namespace}\n'


def run(input_path: Path, directory: Path, namespace: str) -> tuple[dict, int]:
    gram.validate_namespace(namespace)
    require(not directory.exists() or directory.is_dir() and not any(directory.iterdir()),
            'output directory must be new or empty')
    original, c = read_archive(input_path)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'capture.json').write_bytes(original)
    report = dict(format='leanpep-structured-pg-one-v1', mode='archive_structured',
        generation_rule=GENERATION_RULE, residual_recomputed=True, selected_endpoint=None,
        capture_bytes_sha256=CAPTURE_SHA256, live_capture_performed=False, candidate_accepted=False,
        actual_upper_verified=False, d13_acceptance_met=False, primal_certified=False, tightness_claimed=False,
        source_coefficients_changed=False, raw_modified=False, namespace=namespace, status='started')
    try:
        candidate = build_candidate(c)
        audit = audit_candidate(c, candidate)
        pipeline.write_json(directory / 'direct_audit.json', audit)
        require(audit['candidate_diagnostic_accepted'], 'original Python diagnostics rejected structured candidate')
        pipeline.write_json(directory / 'raw_exact.json', sparse.artifact_tree(c.prepared.raw.artifact))
        pipeline.write_json(directory / 'candidate_exact.json', sparse.artifact_tree(candidate))
        replay = directory / 'Replay.lean'
        gram.atomic_write(replay, render_replay(c, candidate, namespace))
        report['candidate_bytes_sha256'] = pipeline.digest(directory / 'candidate_exact.json')
        report['replay_bytes_sha256'] = pipeline.digest(replay)
        report['lean'] = pipeline.check_lean(replay, directory, namespace, True)
        if report['lean']['checked']:
            # Publish the selected file only after the original Lean checks and
            # actual_upper have executed, not merely a Python prediction.
            (directory / 'selected_exact.json').write_bytes((directory / 'candidate_exact.json').read_bytes())
            report.update(candidate_accepted=True, selected_endpoint='structured', actual_upper_verified=True,
                          bound=rational(candidate.upper.bound), status='verified_upper')
        else:
            report['status'] = 'lean_failed_or_unavailable'
        report['interface_smoke_exit'] = pipeline.invoke(
            ['lake', 'env', 'lean', 'tests/lean/smoke/V13D13SmokeTest.lean'], directory / 'interface_smoke.log')
        return report, 0 if report['actual_upper_verified'] and report['interface_smoke_exit'] == 0 else 3
    except Exception as exc:
        report.update(status='failed', error=f'{type(exc).__name__}: {exc}')
        (directory / 'error.log').write_text(traceback.format_exc())
        return report, 1
    finally:
        report['input_bytes_unchanged'] = input_path.read_bytes() == original
        pipeline.write_json(directory / 'structured_report.json', report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--namespace', required=True)
    args = parser.parse_args()
    try:
        report, code = run(args.input, args.output_dir, args.namespace)
        print(pipeline.dump(report))
        return code
    except (ValueError, OSError) as exc:
        parser.exit(1, f'error: {exc}\n')


if __name__ == '__main__':
    raise SystemExit(main())
