"""Original-checker diagnostics on the real 005 archive and adversarial edits.

Unit tests do not claim Lean execution. The separately executed per-run Replay
is the evidence for the actual-function theorem.
"""
import copy
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import prepare_proximal_gradient_candidates as prep
import replay_structured_pg_one as structured

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / 'data/fixtures/pepit_capture/pg_one_live_clarabel_005_20260929.json'


class StructuredPGOneTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original, cls.converted = structured.read_archive(ARCHIVE)
        cls.candidate = structured.build_candidate(cls.converted)

    def test_real_005_positive_and_direct_policy(self):
        c = self.converted
        before = copy.deepcopy(c.capture)
        a = structured.build_candidate(c)
        audit = structured.audit_candidate(c, a)
        self.assertTrue(audit['candidate_diagnostic_accepted'])
        self.assertTrue(all(audit['structured_diagnostic']['compact_certificate'].values()))
        self.assertEqual(a.upper.bound, Q(1, 4))
        self.assertEqual(a.upper.assumption_terms[2].weight, Q(53180, 158821))
        self.assertEqual([t.index for t in a.upper.assumption_terms], list(range(10)))
        self.assertEqual(a.upper.interp_terms, ())
        self.assertEqual((audit['coefficient_count'], audit['changed_count']), (90, 47))
        self.assertEqual(audit['max_abs_error'], dict(num=598900370443981, den=1588210000000000000000))
        self.assertEqual(audit['max_candidate_coefficient_denominator'], 317642)
        self.assertFalse(audit['factor_denominators_subject_to_policy'])
        self.assertEqual(c.capture, before)
        self.assertEqual(ARCHIVE.read_bytes(), self.original)
        self.assertEqual(prep.source_tree(a), prep.source_tree(c.prepared.raw.artifact))
        # Original reconstruction remains the old, rejected endpoint.
        self.assertFalse(c.prepared.report['reconstructed_joint_accepted_diagnostic'])
        self.assertNotEqual(a.upper.dual_matrix, c.prepared.reconstructed.artifact.upper.dual_matrix)

    def test_nonzero_matrix_perturbation_inside_budget_rejected(self):
        a = self.candidate
        S = [list(row) for row in a.upper.dual_matrix]
        self.assertNotEqual(S[0][0], 0)
        S[0][0] += Q(1, 10**6)
        bad = replace(a, upper=replace(a.upper, dual_matrix=tuple(map(tuple, S))))
        audit = structured.audit_candidate(self.converted, bad)
        self.assertTrue(all(audit['policy'].values()))
        self.assertFalse(audit['structured_diagnostic']['compact_certificate']['identity'])
        self.assertFalse(audit['candidate_diagnostic_accepted'])
        with self.assertRaisesRegex(ValueError, 'candidate rejected'):
            structured.render_replay(self.converted, bad, 'LeanPEP.Imported.Test.Structured')

    def test_default_005_path_remains_negative(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = structured.pipeline.select_candidate(
                self.converted, Path(tmp), 'LeanPEP.Imported.Test.Original005', 10000)
        self.assertFalse(result.accepted)
        self.assertIsNone(result.endpoint)
        self.assertEqual(result.proof_kind, 'fixed_family_obstruction')

    def test_valid_upper_outside_raw_budget_rejected(self):
        a = self.candidate
        delta = Q(1, 1000)
        v = (Q(1), Q(0), Q(-1), Q(0), Q(0), Q(0))
        terms = list(a.upper.assumption_terms)
        terms[1] = replace(terms[1], weight=terms[1].weight + delta)
        S = tuple(tuple(a.upper.dual_matrix[i][j] + delta*v[i]*v[j] for j in range(6)) for i in range(6))
        factors = gram.FactorCertSpec(a.upper.dual_factor.factors + (gram.RankOneFactorSpec(delta, v),))
        bad = replace(a, upper=replace(a.upper, bound=a.upper.bound+delta,
                      assumption_terms=tuple(terms), dual_matrix=S, dual_factor=factors))
        audit = structured.audit_candidate(self.converted, bad)
        self.assertTrue(audit['structured_diagnostic']['diagnostic_passed'])
        self.assertFalse(audit['policy']['error_bounds'])
        self.assertFalse(audit['candidate_diagnostic_accepted'])

    def test_cannot_widen_policy_in_memory(self):
        c = self.converted
        policy = replace(c.prepared.policy, max_abs_error=Q(1))
        bad = replace(c, prepared=replace(c.prepared, policy=policy))
        with self.assertRaisesRegex(ValueError, 'policy mismatch'):
            structured.audit_candidate(bad, self.candidate)

    def test_mismatched_source_row_rejected(self):
        d = copy.deepcopy(self.converted.capture)
        d['constraints'][1]['expression']['const'] = dict(num=-2, den=1)
        with self.assertRaises(ValueError):
            structured.build_candidate(cap.convert(d, 1))

    def test_row_labels_not_inferred_from_count(self):
        d = copy.deepcopy(self.converted.capture)
        r = d['constraints']
        r[2]['label'], r[3]['label'] = r[3]['label'], r[2]['label']
        with self.assertRaises(ValueError):
            structured.build_candidate(cap.convert(d, 1))

    def test_changed_ordered_reference_rejected(self):
        a = self.candidate
        terms = list(a.upper.assumption_terms)
        terms[2] = replace(terms[2], index=3)
        bad = replace(a, upper=replace(a.upper, assumption_terms=tuple(terms)))
        audit = structured.audit_candidate(self.converted, bad)
        self.assertFalse(audit['policy']['assumption_references'])
        self.assertFalse(audit['candidate_diagnostic_accepted'])

    def test_zero_multiplier_must_not_be_dropped(self):
        a = self.candidate
        terms = tuple(t for t in a.upper.assumption_terms if t.weight != 0)
        bad = replace(a, upper=replace(a.upper, assumption_terms=terms))
        with self.assertRaisesRegex(ValueError, 'coefficient count mismatch'):
            structured.audit_candidate(self.converted, bad)

    def test_candidate_source_cannot_replace_original(self):
        a = self.candidate
        bad = replace(a, compact_rows=tuple(reversed(a.compact_rows)))
        with self.assertRaisesRegex(ValueError, 'source differs'):
            structured.audit_candidate(self.converted, bad)

    def test_bad_capture_bytes_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'capture.json'
            path.write_bytes(self.original + b'\n')
            with self.assertRaisesRegex(ValueError, 'byte hash mismatch'):
                structured.read_archive(path)

    def test_no_selected_file_when_lean_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'new'
            with mock.patch.object(structured.pipeline, 'check_lean', return_value={'checked': False}), \
                 mock.patch.object(structured.pipeline, 'invoke', return_value=0):
                report, code = structured.run(ARCHIVE, out, 'LeanPEP.Imported.Test.Structured')
            self.assertEqual(code, 3)
            self.assertFalse(report['candidate_accepted'])
            self.assertFalse(report['actual_upper_verified'])
            self.assertFalse((out / 'selected_exact.json').exists())
            with self.assertRaisesRegex(ValueError, 'new or empty'):
                structured.run(ARCHIVE, out, 'LeanPEP.Imported.Test.Structured')


if __name__ == '__main__':
    unittest.main()
