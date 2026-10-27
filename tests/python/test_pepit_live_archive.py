"""Regression for a real D13 failure, not a fabricated accepted endpoint.

Captured by PEPit 0.5.1 / Clarabel 0.11.1 in D13LiveOne_001 on 2026-09-29.
The original bytes and live command/logs are retained in the D13 handoff bundle.
These tests require no solver: source compatibility and fixed-residual failure
are independently rechecked from the archive with exact arithmetic.
"""
from fractions import Fraction as Q
import hashlib
from pathlib import Path
import unittest

import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import complete_pepit_proximal_gradient_capture as completion
import solve_exact_linear_system as linear

ARCHIVE = Path(__file__).resolve().parents[2] / 'data/fixtures/pepit_capture/pg_one_live_clarabel_20260929.json'


class RealCaptureRegression(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = gram.load_json(ARCHIVE)
        cls.result = completion.complete(cls.data, 1)

    def test_real_source_and_raw_binding(self):
        # Byte identity is provenance bookkeeping, not mathematical authority.
        self.assertEqual(hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
                         '4acdd8d2eee0b86d99f7b7fe6f82d37ec10da07a99a09e8eab564eff26bb8e32')
        c = self.result.capture
        self.assertTrue(c.source_passed)
        self.assertTrue(all(cap.trace_diagnostic(c).values()))
        self.assertTrue(all(cap.raw_binding_diagnostic(c, c.prepared.raw.artifact.upper).values()))

    def test_fixed_residual_has_exact_linear_obstruction(self):
        a = self.result
        self.assertEqual(a.linear.status, 'inconsistent')
        self.assertTrue(linear.is_obstruction(a.system, a.linear.obstruction))
        self.assertFalse(a.report['raw_accepted'])
        self.assertFalse(a.report['seed_accepted'])
        self.assertFalse(a.report['completion_accepted'])
        # A small relation suffices; no PSD tolerances or solver floats involved.
        relation = {3: Q(-1, 2), 4: Q(-1, 2), 6: Q(-1, 2),
                    8: Q(1), 10: Q(1), 11: Q(-1), 12: Q(1)}
        for j in range(a.system.columns):
            self.assertEqual(sum(w * a.system.matrix[i][j] for i, w in relation.items()), 0)
        self.assertNotEqual(sum(w * a.system.rhs[i] for i, w in relation.items()), 0)


if __name__ == '__main__':
    unittest.main()
