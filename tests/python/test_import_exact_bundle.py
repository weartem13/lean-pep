#!/usr/bin/env python3
"""Unit and golden tests for the exact JSON-to-Lean importer."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parents[2] / "tools"
ROOT = TOOLS_DIR.parent

import import_exact_bundle as importer  # noqa: E402


class ImportExactBundleTests(unittest.TestCase):
    CASES = (
        (
            "two_step_exact.json",
            "LeanPEP.Imported.TwoStepExact",
            "TwoStepExact.lean",
        ),
        (
            "two_step_bad_metadata.json",
            "LeanPEP.Imported.TwoStepBadMetadata",
            "TwoStepBadMetadata.lean",
        ),
        (
            "two_step_bad_primal.json",
            "LeanPEP.Imported.TwoStepBadPrimal",
            "TwoStepBadPrimal.lean",
        ),
        (
            "two_step_bad_bound.json",
            "LeanPEP.Imported.TwoStepBadBound",
            "TwoStepBadBound.lean",
        ),
    )

    def load_raw(self, filename: str = "two_step_exact.json") -> dict:
        path = ROOT / "data/fixtures" / "external" / filename
        return dict(importer.load_json(path))

    def test_committed_generated_files_are_current(self) -> None:
        for fixture, namespace, lean_name in self.CASES:
            with self.subTest(fixture=fixture):
                raw = self.load_raw(fixture)
                spec = importer.parse_bundle(raw)
                expected = importer.render_module(spec, namespace)
                actual = (ROOT / "LeanPEP" / "Imported" / lean_name).read_text(
                    encoding="utf-8"
                )
                self.assertEqual(actual, expected)

    def test_exact_rationals_reject_json_float(self) -> None:
        raw = self.load_raw()
        raw["primal"]["grad"][0]["num"] = 0.2
        with self.assertRaisesRegex(
            importer.ImportFormatError, "JSON floats are never accepted"
        ):
            importer.parse_bundle(raw)

    def test_wrong_vector_length_is_rejected_before_lean_generation(self) -> None:
        raw = self.load_raw()
        raw["primal"]["grad"].pop()
        with self.assertRaisesRegex(importer.ImportFormatError, "exactly 3 entries"):
            importer.parse_bundle(raw)

    def test_out_of_range_point_index_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["interp_terms"][0]["j"]["index"] = 3
        with self.assertRaisesRegex(importer.ImportFormatError, "outside 0..2"):
            importer.parse_bundle(raw)

    def test_out_of_range_objective_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["objective"] = 3
        with self.assertRaisesRegex(importer.ImportFormatError, "outside 0..2"):
            importer.parse_bundle(raw)

    def test_unknown_field_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["interpolation_terms"] = raw["upper"]["interp_terms"]
        with self.assertRaisesRegex(importer.ImportFormatError, "unknown field"):
            importer.parse_bundle(raw)

    def test_duplicate_json_keys_are_rejected(self) -> None:
        with self.assertRaisesRegex(importer.ImportFormatError, "duplicate key"):
            json.loads(
                '{"schema_version": 1, "schema_version": 1}',
                object_pairs_hook=importer.reject_duplicate_pairs,
            )

    def test_metadata_mismatch_is_preserved_for_lean_auditing(self) -> None:
        raw = self.load_raw("two_step_bad_metadata.json")
        spec = importer.parse_bundle(raw)
        self.assertEqual(spec.declared_constraint_count, 15)
        rendered = importer.render_module(
            spec, "LeanPEP.Imported.TwoStepBadMetadata"
        )
        self.assertIn("declaredConstraintCount := 15", rendered)
        self.assertIn("checkExactBundleQ bundleQ = false", rendered)

    def test_rendering_is_deterministic(self) -> None:
        raw = self.load_raw()
        spec1 = importer.parse_bundle(copy.deepcopy(raw))
        spec2 = importer.parse_bundle(copy.deepcopy(raw))
        self.assertEqual(
            importer.render_module(spec1, "LeanPEP.Imported.Deterministic"),
            importer.render_module(spec2, "LeanPEP.Imported.Deterministic"),
        )


if __name__ == "__main__":
    unittest.main()
