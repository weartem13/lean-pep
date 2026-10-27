#!/usr/bin/env python3
"""Discover the maintenance suite independently of the caller's directory.

Tests are imported as the ``tests.python`` package. The production tools retain
their established standalone sibling imports; this one entry adds their fixed
directory once, without relying on an external PYTHONPATH or per-test changes
to sys.path. Mathematical assertions and fixture acceptance remain in the tests.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]


def cases(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from cases(item)
        else:
            yield item


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true', help='list every discovered test without running it')
    parser.add_argument('--pattern', default='test_*.py', help='unittest discovery filename pattern')
    parser.add_argument('--inventory-json', type=Path, help='write the exact discovered test IDs')
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args(argv)

    # One documented compatibility boundary for the standalone production tools.
    for path in reversed([str(ROOT), str(ROOT / 'tools')]):
        if path in sys.path:
            sys.path.remove(path)
        sys.path.insert(0, path)
    loader = unittest.TestLoader()
    suite = loader.discover(str(ROOT / 'tests/python'), pattern=args.pattern,
                            top_level_dir=str(ROOT))
    ids = [test.id() for test in cases(suite)]
    inventory = {'source_root': str(ROOT), 'count': len(ids), 'ids': ids,
                 'import_errors': loader.errors}
    if args.inventory_json:
        args.inventory_json.parent.mkdir(parents=True, exist_ok=True)
        args.inventory_json.write_text(json.dumps(inventory, indent=2, sort_keys=True) + '\n')
    if args.list:
        print('\n'.join(ids))
        print(f'Discovered {len(ids)} tests; {len(loader.errors)} import errors.')
        if loader.errors:
            print('\n'.join(loader.errors), file=sys.stderr)
        return 1 if loader.errors else 0
    if not ids:
        parser.error('no tests discovered')
    return 0 if unittest.TextTestRunner(verbosity=2 if args.verbose else 1).run(suite).wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
