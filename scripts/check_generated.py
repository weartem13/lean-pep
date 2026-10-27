#!/usr/bin/env python3
"""Regenerate retained deterministic fixtures in a fresh external snapshot.

The existing generator shell is executed unchanged. The source tree is never
an output destination; no Lean build, solver, or live capture is invoked.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
TREES = ('tools', 'data/fixtures', 'LeanPEP')
CACHE_NAMES = {'__pycache__', '.pytest_cache'}
# Only these documentary JSON leaves may describe a migrated input pathname.
# Numeric strings, labels, references, hashes and Lean modules are never normalized.
PATH_METADATA_KEYS = {'origin', 'source_path', 'input_path', 'output_path', 'path', 'file'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def fresh_output(root, output):
    root = root.resolve()
    output = output.absolute()
    if output.is_symlink() or output.exists():
        raise ValueError('output must be a fresh absent directory')
    resolved = output.resolve()
    if resolved == root or root in resolved.parents:
        raise ValueError('output must be outside the source tree')
    for parent in output.parents:
        if parent.is_symlink():
            raise ValueError('output ancestors must not be symlinks')
    output.mkdir(parents=True)
    return output


def source_files(root):
    files = {}
    for relative in TREES:
        directory = root / relative
        if not directory.is_dir() or directory.is_symlink():
            raise ValueError('missing or symbolic source directory: ' + relative)
        for current, directories, names in os.walk(directory, followlinks=False):
            current = Path(current)
            for name in [*directories, *names]:
                path = current / name
                if path.is_symlink():
                    raise ValueError('symbolic source entry refused: ' + str(path.relative_to(root)))
            directories[:] = [name for name in directories if name not in CACHE_NAMES]
            for name in names:
                path = current / name
                if path.suffix in {'.pyc', '.olean', '.ilean'}:
                    continue
                if not path.is_file():
                    raise ValueError('nonregular source entry refused: ' + str(path.relative_to(root)))
                files[path.relative_to(root).as_posix()] = digest(path)
    return dict(sorted(files.items()))


def json_differences(before, after, location=()):
    if type(before) is not type(after):
        return [(location, before, after)]
    if isinstance(before, dict):
        if before.keys() != after.keys():
            return [(location, before, after)]
        return [item for key in before for item in json_differences(before[key], after[key], (*location, key))]
    if isinstance(before, list):
        if len(before) != len(after):
            return [(location, before, after)]
        return [item for index, (a, b) in enumerate(zip(before, after))
                for item in json_differences(a, b, (*location, index))]
    return [] if before == after else [(location, before, after)]


def compare_payload(relative, before, after):
    if before == after:
        return {'status': 'byte_identical', 'differences': []}
    if Path(relative).suffix != '.json':
        return {'status': 'unexpected_difference', 'differences': [], 'reason': 'non-JSON bytes changed'}
    try:
        differences = json_differences(json.loads(before), json.loads(after))
    except (ValueError, UnicodeError):
        return {'status': 'unexpected_difference', 'differences': [], 'reason': 'JSON parse failure'}
    allowed = bool(differences) and all(
        location and location[-1] in PATH_METADATA_KEYS and isinstance(a, str) and isinstance(b, str)
        and 'examples/' in a and a.replace('examples/', 'data/fixtures/') == b
        for location, a, b in differences)
    return {'status': 'documented_metadata_path_only' if allowed else 'unexpected_difference',
            'differences': [{'path': '/' + '/'.join(map(str, location)), 'before': a, 'after': b}
                            for location, a, b in differences]}


def run(root, output, timeout):
    root = root.resolve()
    output = fresh_output(root, output)
    report = {'status': 'started', 'source_root': str(root), 'output': str(output),
              'solver_calls': 0, 'lean_executed': False, 'generator_policy_changed': False,
              'comparison_policy': 'Exact file bytes; JSON documentary path leaves alone may replace examples/ by data/fixtures/.',
              'command': None}
    before = source_files(root)
    write(output / 'source-before.json', before)
    snapshot = output / 'snapshot'
    snapshot.mkdir()
    for relative in before:
        destination = snapshot / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / relative, destination)
    copied = source_files(snapshot)
    if copied != before:
        raise ValueError('snapshot copy differs from source')
    initial_stats = {name: ((snapshot / name).stat().st_mtime_ns, (snapshot / name).stat().st_ino)
                     for name in before}
    env = os.environ.copy()
    for key in ('LEAN_PATH', 'PYTHONPATH', 'LEAN_SRC_PATH', 'LAKE_HOME'):
        env.pop(key, None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['PATH'] = str(Path(sys.executable).parent) + os.pathsep + env.get('PATH', '')
    python3 = shutil.which('python3', path=env['PATH'])
    if not python3 or Path(python3).resolve() != Path(sys.executable).resolve():
        raise ValueError('the current Python installation must provide a matching python3 executable')
    argv = ['bash', 'tools/regenerate_imported_examples.sh']
    command = {'cwd': str(snapshot), 'argv': argv, 'timeout_seconds': timeout,
               'python_executable': python3,
               'environment': {'LEAN_PATH': 'unset', 'PYTHONPATH': 'unset', 'PYTHONDONTWRITEBYTECODE': '1'},
               'started_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'log': 'generation.log'}
    started = time.monotonic()
    with (output / 'generation.log').open('w') as log:
        process = subprocess.Popen(argv, cwd=snapshot, env=env, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            code = 124
    command.update(exit=code, wall_seconds=time.monotonic() - started)
    report['command'] = command
    write(output / 'command.json', command)
    after = source_files(snapshot)
    write(output / 'snapshot-after.json', after)
    rows = []
    for relative in sorted(set(before) | set(after)):
        if relative not in before or relative not in after:
            comparison = {'status': 'unexpected_file_set_change', 'differences': []}
        else:
            comparison = compare_payload(relative, (root / relative).read_bytes(), (snapshot / relative).read_bytes())
        changed_stamp = relative in after and (
            relative not in initial_stats or initial_stats[relative] != (
                (snapshot / relative).stat().st_mtime_ns, (snapshot / relative).stat().st_ino))
        rows.append(dict(path=relative, before_sha256=before.get(relative), after_sha256=after.get(relative),
                         observed_rewrite=changed_stamp, **comparison))
    final_source = source_files(root)
    write(output / 'source-after.json', final_source)
    source_unchanged = final_source == before
    unexpected = [row for row in rows if row['status'].startswith('unexpected')]
    report.update(status='passed' if code == 0 and source_unchanged and not unexpected else 'failed',
                  source_unchanged=source_unchanged, compared_files=len(rows),
                  observed_rewrites=sum(row['observed_rewrite'] for row in rows),
                  byte_identical=sum(row['status'] == 'byte_identical' for row in rows),
                  metadata_path_only=sum(row['status'] == 'documented_metadata_path_only' for row in rows),
                  unexpected_differences=unexpected, files=rows)
    write(output / 'result.json', report)
    print(json.dumps({key: value for key, value in report.items() if key not in {'files', 'unexpected_differences'}}, indent=2))
    return 0 if report['status'] == 'passed' else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='fresh absent directory outside the source tree')
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    return run(ROOT, args.output, args.timeout)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print('error: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
