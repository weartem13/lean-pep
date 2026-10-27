#!/usr/bin/env python3
"""D13 integration entry: real PEPit capture or byte-preserving archive replay.

No new mathematical checker. Dispatch raw -> reconstructed -> fixed-residual
D11 completion/D12 binding, and run the generated Lean proof. Missing runtimes,
source rejection, candidate failure, proof failure and skipped Lean remain
separate statuses. Replay never claims this invocation performed a live solve.
"""
from __future__ import annotations

import argparse
import contextlib
from dataclasses import dataclass
import hashlib
import importlib
import importlib.metadata
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import traceback
from typing import Any

import import_exact_gram_bundle as gram
import capture_pepit_proximal_gradient as exporter
import import_pepit_proximal_gradient_capture as cap
import prepare_proximal_gradient_candidates as prep
import import_proximal_gradient_sparse as sparse
import audit_compiled_completion as compiler

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def dump(data: Any) -> str:
    return json.dumps(data, indent=2, sort_keys=True, allow_nan=False) + '\n'


def write_json(path: Path, data: Any) -> None:
    gram.atomic_write(path, dump(data))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_outputs(outputs: dict[Path, str]) -> None:
    for path, text in outputs.items():
        gram.atomic_write(path, text)


def runtime_info(solver: str, live: bool, *, require_solver: bool = True) -> dict[str, Any]:
    """Observe actual installed packages. Hashes are records, not authentication."""
    packages = {}
    errors = []
    for name in ('PEPit', 'cvxpy', 'clarabel', 'numpy', 'scipy', 'pandas'):
        try:
            packages[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            packages[name] = None
    result = dict(python=sys.version, executable=sys.executable, platform=platform.platform(),
        packages=packages, lake=shutil.which('lake'), requested_solver=solver,
        producer_authenticated=False, pepit_source_hashes={})
    if live:
        if packages['PEPit'] != cap.SUPPORTED_PEPIT:
            errors.append('PEPit ' + cap.SUPPORTED_PEPIT + ' is required')
        try:
            pepit = importlib.import_module('PEPit')
            root = Path(pepit.__file__).resolve().parent
            result['pepit_source_hashes'] = {
                str(p.relative_to(root)): digest(p) for p in sorted(root.rglob('*.py'))}
        except (ImportError, OSError) as exc:
            errors.append('PEPit import: ' + str(exc))
        if require_solver:
            try:
                cp = importlib.import_module('cvxpy')
                installed = cp.installed_solvers()
                result['installed_solvers'] = installed
                if solver not in installed:
                    errors.append('requested solver is not installed in CVXPY: ' + solver)
            except ImportError as exc:
                errors.append('CVXPY import: ' + str(exc))
    result['capture_runtime_errors'] = errors
    result['capture_runtime_ready'] = live and not errors
    return result


@dataclass(frozen=True)
class Selection:
    endpoint: str | None
    accepted: bool
    proof_kind: str
    replay: str
    bound: dict[str, int] | None
    report: dict[str, Any]


def endpoint_replay(converted: cap.Converted, namespace: str, endpoint: str) -> str:
    """Use D9's existing theorem; no formula for the expected bound is injected."""
    if endpoint not in ('raw', 'reconstructed') or converted.prepared is None:
        raise ValueError('no accepted numeric endpoint to render')
    raw = converted.prepared.raw.artifact.upper
    trace_ok = all(cap.trace_diagnostic(converted).values())
    binding_ok = all(cap.raw_binding_diagnostic(converted, raw).values())
    raw_ok = trace_ok and binding_ok and converted.prepared.report['raw_accepted_diagnostic']
    rec_ok = trace_ok and binding_ok and converted.prepared.report['reconstructed_joint_accepted_diagnostic']
    if not (raw_ok if endpoint == 'raw' else rec_ok):
        raise ValueError('selected endpoint did not pass its independent audit')
    text = cap.render_module(converted, namespace).replace('import ' + cap.AS, 'import LeanPEP', 1)
    # Rendering is a proof candidate. The runner only records kernel success
    # after a real Lean command and the explicit actual_upper axiom output.
    text += f'\nnamespace {namespace}\nopen LeanPEP.GramPEP\n'
    text += f'''theorem raw_track_check : {cap.AS}.checkCapturedRawQ sourceQ traceQ rawUpperQ = {str(raw_ok).lower()} := by
  decide +kernel
theorem reconstructed_track_check : {cap.AS}.checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = {str(rec_ok).lower()} := by
  decide +kernel
open scoped NNReal
'''
    T = converted.capture['horizon']
    upper = 'rawUpperQ' if endpoint == 'raw' else 'reconstructedUpperQ'
    proof = ('LeanPEP.ActualFunction.ProximalGradientCaptureAudit.raw_upper_firstOrder '
             'sourceQ traceQ rawUpperQ raw_track_check hf.toFirstOrder' if endpoint == 'raw' else
             'LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic '
             'sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ reconstructed_track_check hf')
    text += f'''theorem actual_upper {{E : Type*}} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {{L : ℝ≥0}} {{R : ℝ}} {{f h : E → ℝ}} {{g : E → E}} {{xStar : E}} {{x : ℕ → E}}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun {T} L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x {T}) + h (x {T}) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * ({upper}.bound : ℝ) :=
  {proof} hh hL hR hmin hrun hradius
#print axioms raw_track_check
#print axioms reconstructed_track_check
#print axioms actual_upper
end {namespace}
'''
    return text


def select_candidate(converted: cap.Converted, directory: Path, namespace: str,
                     max_pivots: int) -> Selection:
    if converted.prepared is None:
        raise ValueError('prepared-only archive has no numerical candidate')
    if not converted.source_passed or not all(cap.trace_diagnostic(converted).values()):
        raise ValueError('source audit failed')
    p = converted.prepared
    binding = cap.raw_binding_diagnostic(converted, p.raw.artifact.upper)
    raw_ok = all(binding.values()) and p.report['raw_accepted_diagnostic']
    rec_ok = all(binding.values()) and p.report['reconstructed_joint_accepted_diagnostic']
    report = dict(raw_accepted=bool(raw_ok), reconstructed_accepted=bool(rec_ok),
        completion_attempted=False, raw_binding=binding)
    if raw_ok or rec_ok:
        endpoint = 'raw' if raw_ok else 'reconstructed'
        a = p.raw.artifact if raw_ok else p.reconstructed.artifact
        write_json(directory / 'selected_exact.json', sparse.artifact_tree(a))
        return Selection(endpoint, True, 'actual_upper', endpoint_replay(converted, namespace, endpoint),
            dict(num=a.upper.bound.numerator, den=a.upper.bound.denominator), report)
    # D12 runs unchanged D10/D11 and binds the submitted system to the old model.
    a = compiler.run(converted.capture, 'box', converted.capture['horizon'], max_pivots=max_pivots)
    write_outputs(compiler.outputs(a, directory / 'completion', namespace))
    ok = bool(a.report['binding_diagnostic_passed'] and a.report['previous_completion_accepted'])
    report.update(completion_attempted=True, compiler_binding=a.report,
        completion_report=a.result.report)
    b = a.result.artifact.upper.bound if ok else None
    kind = 'actual_upper' if ok else ('fixed_family_obstruction'
        if a.report['binding_diagnostic_passed'] and a.result.result.obstruction is not None else 'diagnostic')
    if ok:
        write_json(directory / 'selected_exact.json', sparse.artifact_tree(a.result.artifact))
    return Selection('completed' if ok else None, ok, kind, compiler.render_binding_replay(a, namespace),
        None if b is None else dict(num=b.numerator, den=b.denominator), report)


def invoke(command: list[str], log: Path) -> int:
    """No shell; invoke the user's pinned project toolchain from its root."""
    with log.open('w', encoding='utf-8') as handle:
        handle.write('$ ' + ' '.join(command) + '\n')
        handle.flush()
        return subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT,
                              check=False).returncode


def axiom_output_ok(output: str, namespace: str, positive: bool) -> bool:
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    ours = [(name, {x.strip() for x in values.split(',') if x.strip()})
            for name, values in matches if name.startswith(namespace + '.')]
    return (bool(ours) and all(values <= ALLOWED_AXIOMS for _, values in ours)
            and (not positive or any(name == namespace + '.actual_upper' for name, _ in ours)))


def check_lean(replay: Path, directory: Path, namespace: str, positive: bool) -> dict[str, Any]:
    lake = shutil.which('lake')
    result = dict(attempted=False, build_exit=None, replay_exit=None, axioms_allowed=False,
                  checked=False, reason=None)
    if lake is None:
        result['reason'] = 'lake_unavailable'
        return result
    result['attempted'] = True
    result['build_exit'] = invoke([lake, 'build', 'LeanPEP'], directory / 'lean_build.log')
    if result['build_exit'] != 0:
        result['reason'] = 'build_failed'
        return result
    result['replay_exit'] = invoke([lake, 'env', 'lean', str(replay.resolve())], directory / 'lean_replay.log')
    if result['replay_exit'] != 0:
        result['reason'] = 'replay_failed'
        return result
    output = (directory / 'lean_replay.log').read_text()
    result['axioms_allowed'] = axiom_output_ok(output, namespace, positive)
    result['checked'] = result['axioms_allowed']
    result['reason'] = None if result['checked'] else 'missing_or_unexpected_axiom_output'
    return result


class SourceRejected(ValueError):
    pass


def run_pipeline(mode: str, directory: Path, *, input_path: Path | None = None,
                 steps: int = 1, solver: str = 'CLARABEL', namespace: str = 'LeanPEP.Imported.Live.PGOne',
                 max_denominator: int = 1000000, max_abs_error: str = '0.000001',
                 max_pivots: int = 10000, solver_options: dict[str, Any] | None = None,
                 skip_lean: bool = False, prepare_only: bool = False) -> tuple[dict[str, Any], int]:
    if mode not in ('live', 'replay'):
        raise ValueError('mode must be live or replay')
    if type(steps) is not int or steps < 1 or type(max_pivots) is not int or max_pivots < 0:
        raise ValueError('invalid horizon or pivot limit')
    gram.validate_namespace(namespace)
    prep._policy(dict(method='limit_denominator', max_denominator=max_denominator, max_abs_error=max_abs_error))
    if mode == 'replay' and input_path is None:
        raise ValueError('replay requires a capture input')
    if prepare_only and mode != 'live':
        raise ValueError('prepare-only is a live command option')
    if directory.exists() and (not directory.is_dir() or any(directory.iterdir())):
        raise ValueError('output directory must be absent or empty; no stale success artifacts allowed')
    if input_path is not None and directory.resolve() == input_path.resolve():
        raise ValueError('output cannot replace input')
    directory.mkdir(parents=True, exist_ok=True)
    r: dict[str, Any] = dict(format='leanpep-pg-pipeline-v1', mode=mode, horizon=steps,
        status='started', live_capture_performed=False, producer_claim=None, producer_authenticated=False,
        source_passed=False, candidate_accepted=False, selected_endpoint=None, bound=None,
        proof_kind=None, lean_checked=False, actual_upper_verified=False, d13_acceptance_met=False,
        primal_feasibility_checked=False, tightness_claimed=False, source_coefficients_changed=False,
        residual_recomputed=False, error=None,
        configuration=dict(namespace=namespace, max_pivots=max_pivots, skip_lean=skip_lean,
            prepare_only=prepare_only, requested_solver=solver if mode=='live' else None,
            solver_options=json.loads(dump(solver_options or {})) if mode=='live' else None))
    code = 1
    try:
        env = runtime_info(solver, mode == 'live', require_solver=not prepare_only)
        write_json(directory / 'environment.json', env)
        if mode == 'live' and env['capture_runtime_errors']:
            r.update(status='runtime_unavailable', error='; '.join(env['capture_runtime_errors']))
            return r, 1
        if mode == 'live':
            def observe(stage: str, payload: dict[str, Any]) -> None:
                if stage == 'prepared':
                    write_json(directory / 'prepared_capture.json', payload)
                    c = cap.convert(payload, steps)
                    write_outputs(cap.outputs(c, directory / 'prepared_audit', namespace + '.Prepared'))
                    r['source_passed'] = c.source_passed
                    if not c.source_passed or not all(cap.trace_diagnostic(c).values()):
                        raise SourceRejected('prepared source rejected before numerical solve')
                elif stage == 'capture':
                    write_json(directory / 'capture.json', payload)
                    r['live_capture_performed'] = True
                    r['producer_claim'] = payload['producer']
                elif stage == 'primal':
                    write_json(directory / 'primal_observation.json', payload)
                else:
                    raise ValueError('unknown capture observer stage')
            with (directory / 'capture.log').open('w', encoding='utf-8') as log:
                with contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
                    data = exporter.capture(steps, solver, prepare_only, max_denominator, max_abs_error,
                        2, solver_options, observer=observe)
            if prepare_only:
                r.update(status='prepared_only', producer_claim=data['producer'], proof_kind='source_only')
                return r, 0
            if data['producer']['solver'] != solver:
                r.update(status='solver_mismatch', error='actual solver differs from requested solver')
                return r, 1
        else:
            # Preserve the exact archive bytes; the importer reads without mutation.
            original = input_path.read_bytes()
            (directory / 'capture.json').write_bytes(original)
            data = gram.load_json(directory / 'capture.json')
            r['input_sha256'] = hashlib.sha256(original).hexdigest()
        r['producer_claim'] = data.get('producer')
        r['effective_policy'] = data.get('policy')
        converted = cap.convert(data, steps)
        write_outputs(cap.outputs(converted, directory / 'audit', namespace))
        r['source_passed'] = converted.source_passed and all(cap.trace_diagnostic(converted).values())
        if not r['source_passed']:
            raise SourceRejected('captured source rejected')
        if converted.prepared is None:
            r.update(status='prepared_only', proof_kind='source_only')
            return r, 0
        selection = select_candidate(converted, directory, namespace, max_pivots)
        r.update(selected_endpoint=selection.endpoint, candidate_accepted=selection.accepted,
            proof_kind=selection.proof_kind, bound=selection.bound, selection=selection.report)
        replay = directory / 'Replay.lean'
        gram.atomic_write(replay, selection.replay)
        if skip_lean:
            r.update(status='candidate_ready' if selection.accepted else 'candidate_rejected',
                lean=dict(attempted=False, checked=False, reason='explicitly_skipped'))
            return r, 0 if selection.accepted else 2
        lean = check_lean(replay, directory, namespace, selection.accepted)
        r['lean'] = lean
        r['lean_checked'] = lean['checked']
        r['actual_upper_verified'] = selection.accepted and lean['checked']
        r['d13_acceptance_met'] = r['live_capture_performed'] and r['actual_upper_verified']
        r['status'] = ('verified_upper' if r['actual_upper_verified'] else
            'verified_obstruction' if lean['checked'] and selection.proof_kind == 'fixed_family_obstruction'
            else 'candidate_rejected' if not selection.accepted else 'lean_unavailable_or_failed')
        code = 0 if r['actual_upper_verified'] else 2 if not selection.accepted else 3
        return r, code
    except SourceRejected as exc:
        r.update(status='source_rejected', error=str(exc))
        return r, 2
    except Exception as exc:
        # Preserve partially completed capture/audit artifacts; never manufacture
        # an accepted candidate in an exception path. Full details in error.log.
        r.update(status='failed', error=type(exc).__name__ + ': ' + str(exc))
        (directory / 'error.log').write_text(traceback.format_exc())
        return r, 1
    finally:
        if (directory / 'capture.json').exists():
            r['capture_bytes_sha256'] = digest(directory / 'capture.json')
        write_json(directory / 'pipeline_report.json', r)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='mode', required=True)
    for mode in ('live', 'replay'):
        p = commands.add_parser(mode)
        if mode == 'replay':
            p.add_argument('input', type=Path)
        else:
            p.add_argument('--solver', default='CLARABEL')
            p.add_argument('--solver-options', default='{}')
            p.add_argument('--prepare-only', action='store_true')
            p.add_argument('--max-denominator', type=int, default=1000000)
            p.add_argument('--max-abs-error', default='0.000001')
        p.add_argument('--steps', type=int, default=1)
        p.add_argument('--output-dir', type=Path, required=True)
        p.add_argument('--namespace', default='LeanPEP.Imported.Live.PGOne')
        p.add_argument('--max-pivots', type=int, default=10000)
        p.add_argument('--skip-lean', action='store_true', help='candidate preparation only; never claim kernel verification')
    args = parser.parse_args(argv)
    try:
        options = json.loads(getattr(args, 'solver_options', '{}'))
        if not isinstance(options, dict):
            raise ValueError('solver options must be a JSON object')
        # Do not allow dimension-reduction or wrapper overrides via kwargs.
        reserved = {'wrapper', 'solver', 'dimension_reduction_heuristic', 'return_primal_or_dual',
                    'verbose', 'safe_mode', 'eig_regularization', 'tol_dimension_reduction'}
        if reserved.intersection(options):
            raise ValueError('reserved solver option')
        dump(options)  # rejects NaN/infinity before starting a run
        report, code = run_pipeline(args.mode, args.output_dir, input_path=getattr(args, 'input', None),
            steps=args.steps, solver=getattr(args, 'solver', 'CLARABEL'), namespace=args.namespace,
            max_denominator=getattr(args, 'max_denominator', 1000000),
            max_abs_error=getattr(args, 'max_abs_error', '0.000001'),
            max_pivots=args.max_pivots, solver_options=options, skip_lean=args.skip_lean,
            prepare_only=getattr(args, 'prepare_only', False))
        print(json.dumps({k: report[k] for k in ('status', 'live_capture_performed', 'candidate_accepted',
            'selected_endpoint', 'bound', 'lean_checked', 'actual_upper_verified', 'd13_acceptance_met')},
            sort_keys=True))
        return code
    except (ValueError, OSError) as exc:
        print('error: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
