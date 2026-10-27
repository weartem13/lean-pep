#!/usr/bin/env python3
"""Unit, policy, hash, and golden tests for approximate bundle preparation."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parents[2] / "tools"
ROOT = TOOLS_DIR.parent

import import_exact_bundle as exact  # noqa: E402
import prepare_approx_bundle as approx  # noqa: E402


class PrepareApproxBundleTests(unittest.TestCase):
    SOURCE = ROOT / "data/fixtures" / "approximate" / "two_step_near_exact.json"
    RAW_JSON = ROOT / "data/fixtures" / "generated" / "two_step_near_exact_raw.json"
    RECONSTRUCTED_JSON = (
        ROOT / "data/fixtures" / "generated" / "two_step_near_exact_reconstructed.json"
    )
    REPORT_JSON = (
        ROOT
        / "data/fixtures"
        / "generated"
        / "two_step_near_exact_reconstruction_report.json"
    )
    MANIFEST_JSON = (
        ROOT
        / "data/fixtures"
        / "generated"
        / "two_step_near_exact_comparison_manifest.json"
    )
    RAW_LEAN = ROOT / "LeanPEP" / "Imported" / "TwoStepApproxRaw.lean"
    RECONSTRUCTED_LEAN = (
        ROOT / "LeanPEP" / "Imported" / "TwoStepApproxReconstructed.lean"
    )
    COMPARISON_LEAN = (
        ROOT / "LeanPEP" / "Imported" / "TwoStepApproxComparison.lean"
    )
    RAW_NAMESPACE = "LeanPEP.Imported.TwoStepApproxRaw"
    RECONSTRUCTED_NAMESPACE = "LeanPEP.Imported.TwoStepApproxReconstructed"
    COMPARISON_NAMESPACE = "LeanPEP.Imported.TwoStepApproxComparison"

    def load_raw(self) -> dict:
        return dict(approx.load_json(self.SOURCE))

    def prepare(self, raw: dict | None = None) -> approx.PreparedArtifacts:
        return approx.prepare_artifacts(
            self.load_raw() if raw is None else raw,
            raw_namespace=self.RAW_NAMESPACE,
            reconstructed_namespace=self.RECONSTRUCTED_NAMESPACE,
            comparison_namespace=self.COMPARISON_NAMESPACE,
        )

    def test_committed_generated_files_are_current(self) -> None:
        artifacts = self.prepare()
        rendered = approx.rendered_outputs(artifacts)
        paths = (
            self.RAW_JSON,
            self.RECONSTRUCTED_JSON,
            self.REPORT_JSON,
            self.MANIFEST_JSON,
            self.COMPARISON_LEAN,
        )
        for path, expected in zip(paths, rendered, strict=True):
            with self.subTest(path=path):
                self.assertEqual(path.read_text(encoding="utf-8"), expected)

        raw_spec = exact.parse_bundle(artifacts.raw_exact)
        reconstructed_spec = exact.parse_bundle(artifacts.reconstructed_exact)
        self.assertEqual(
            self.RAW_LEAN.read_text(encoding="utf-8"),
            exact.render_module(raw_spec, self.RAW_NAMESPACE),
        )
        self.assertEqual(
            self.RECONSTRUCTED_LEAN.read_text(encoding="utf-8"),
            exact.render_module(
                reconstructed_spec, self.RECONSTRUCTED_NAMESPACE
            ),
        )

    def test_candidate_json_float_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["primal"]["grad"][0] = 0.2
        with self.assertRaisesRegex(
            approx.ApproxFormatError, "expected a string"
        ):
            self.prepare(raw)

    def test_policy_json_float_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["policy"]["max_abs_error"] = 5e-10
        with self.assertRaisesRegex(
            approx.ApproxFormatError, "expected a string"
        ):
            self.prepare(raw)

    def test_duplicate_json_keys_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "duplicate.json"
            path.write_text(
                '{"schema_version": 1, "schema_version": 1}',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(approx.ApproxFormatError, "duplicate key"):
                approx.load_json(path)

    def test_unknown_fields_are_rejected(self) -> None:
        raw = self.load_raw()
        raw["policy"]["tolerance"] = "1e-6"
        with self.assertRaisesRegex(approx.ApproxFormatError, "unknown field"):
            self.prepare(raw)

    def test_nan_and_infinity_are_rejected(self) -> None:
        for invalid in ("NaN", "Infinity", "-Infinity", "nan"):
            with self.subTest(invalid=invalid):
                raw = self.load_raw()
                raw["upper"]["bound"] = invalid
                with self.assertRaisesRegex(
                    approx.ApproxFormatError, "finite base-10 decimal string"
                ):
                    self.prepare(raw)

    def test_scientific_notation_is_interpreted_exactly(self) -> None:
        artifacts = self.prepare()
        entry = next(
            item
            for item in artifacts.report["entries"]
            if item["path"] == "$.primal.grad[0]"
        )
        self.assertEqual(entry["source"], "2e-1")
        self.assertEqual(entry["source_exact"], {"num": 1, "den": 5})
        self.assertEqual(entry["reconstructed"], {"num": 1, "den": 5})

    def test_raw_and_reconstructed_semantics_are_distinct(self) -> None:
        artifacts = self.prepare()
        raw_value = artifacts.raw_exact["primal"]["value"][0]
        reconstructed_value = artifacts.reconstructed_exact["primal"]["value"][0]
        self.assertEqual(raw_value, {"num": 899999999, "den": 5000000000})
        self.assertEqual(reconstructed_value, {"num": 9, "den": 50})
        self.assertEqual(artifacts.raw_exact["expect"], "rejected")
        self.assertEqual(artifacts.reconstructed_exact["expect"], "accepted")

    def test_reconstruction_respects_denominator_and_error_bounds(self) -> None:
        artifacts = self.prepare()
        report = artifacts.report
        max_denominator = report["policy"]["max_denominator"]
        max_error_obj = report["policy"]["max_abs_error_exact"]
        max_error = Fraction(max_error_obj["num"], max_error_obj["den"])
        for entry in report["entries"]:
            with self.subTest(path=entry["path"]):
                reconstructed = entry["reconstructed"]
                self.assertLessEqual(reconstructed["den"], max_denominator)
                error_obj = entry["absolute_error"]
                error = Fraction(error_obj["num"], error_obj["den"])
                self.assertLessEqual(error, max_error)

    def test_too_small_error_bound_is_rejected_without_silent_repair(self) -> None:
        raw = self.load_raw()
        raw["policy"]["max_abs_error"] = "1e-12"
        with self.assertRaisesRegex(
            approx.ApproxFormatError, "reconstruction error.*exceeds"
        ):
            self.prepare(raw)

    def test_hash_chain_is_exact_and_complete(self) -> None:
        raw = self.load_raw()
        artifacts = self.prepare(raw)
        hashes = artifacts.manifest["hashes"]
        self.assertEqual(hashes["source_sha256"], approx.canonical_sha256(raw))
        self.assertEqual(
            hashes["raw_exact_sha256"],
            approx.canonical_sha256(artifacts.raw_exact),
        )
        self.assertEqual(
            hashes["reconstructed_exact_sha256"],
            approx.canonical_sha256(artifacts.reconstructed_exact),
        )
        self.assertEqual(
            hashes["reconstruction_report_sha256"],
            approx.canonical_sha256(artifacts.report),
        )
        manifest_hash = approx.canonical_sha256(artifacts.manifest)
        self.assertIn(manifest_hash, artifacts.comparison_lean)

    def test_exact_schema_v1_is_reused_unchanged(self) -> None:
        artifacts = self.prepare()
        raw_spec = exact.parse_bundle(artifacts.raw_exact)
        reconstructed_spec = exact.parse_bundle(artifacts.reconstructed_exact)
        self.assertEqual(raw_spec.steps, 2)
        self.assertEqual(reconstructed_spec.steps, 2)
        self.assertEqual(artifacts.raw_exact["schema_version"], exact.SCHEMA_VERSION)
        self.assertEqual(
            artifacts.reconstructed_exact["schema_version"], exact.SCHEMA_VERSION
        )
        self.assertNotIn("policy", artifacts.raw_exact)
        self.assertNotIn("policy", artifacts.reconstructed_exact)

    def test_rendering_is_deterministic(self) -> None:
        raw = self.load_raw()
        first = self.prepare(copy.deepcopy(raw))
        second = self.prepare(copy.deepcopy(raw))
        self.assertEqual(approx.rendered_outputs(first), approx.rendered_outputs(second))

    def test_check_mode_detects_stale_output(self) -> None:
        artifacts = self.prepare()
        rendered = approx.rendered_outputs(artifacts)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = approx.OutputPaths(
                raw_exact=root / "raw.json",
                reconstructed_exact=root / "reconstructed.json",
                report=root / "report.json",
                manifest=root / "manifest.json",
                comparison_lean=root / "comparison.lean",
            )
            approx.write_or_check_outputs(paths, rendered, check=False)
            approx.write_or_check_outputs(paths, rendered, check=True)
            paths.report.write_text("{}\n", encoding="utf-8")
            with self.assertRaisesRegex(approx.ApproxFormatError, "stale"):
                approx.write_or_check_outputs(paths, rendered, check=True)


if __name__ == "__main__":
    unittest.main()
