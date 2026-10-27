#!/usr/bin/env python3
"""Tests for the version-pinned PEPit one-step formulation adapter."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parents[2] / "tools"
ROOT = TOOLS_DIR.parent

import adapt_pepit_one_step as adapter  # noqa: E402
import import_exact_bundle as base  # noqa: E402
import import_exact_gram_bundle as exact  # noqa: E402
import prepare_approx_gram_bundle as prep  # noqa: E402


class AdaptPEPitOneStepTests(unittest.TestCase):
    SOURCE = ROOT / "data/fixtures" / "pepit" / "one_step_gd_solver_artifact.json"
    BAD_ORDER_SOURCE = (
        ROOT / "data/fixtures" / "pepit" / "one_step_gd_bad_constraint_order.json"
    )
    BAD_SYMBOLIC_SOURCE = (
        ROOT / "data/fixtures" / "pepit" / "one_step_gd_bad_symbolic_coefficient.json"
    )
    OUT = ROOT / "data/fixtures" / "pepit_generated"
    APPROX = OUT / "one_step_gd_approximate_gram.json"
    REPORT = OUT / "one_step_gd_adapter_report.json"
    MANIFEST = OUT / "one_step_gd_adapter_manifest.json"
    LEAN = ROOT / "LeanPEP" / "Imported" / "PEPitOneStepAdapter.lean"
    BAD_APPROX = OUT / "one_step_gd_bad_constraint_order_approximate_gram.json"
    BAD_REPORT = OUT / "one_step_gd_bad_constraint_order_adapter_report.json"
    BAD_MANIFEST = OUT / "one_step_gd_bad_constraint_order_adapter_manifest.json"
    BAD_LEAN = (
        ROOT
        / "LeanPEP"
        / "Imported"
        / "PEPitOneStepBadConstraintOrderAdapter.lean"
    )
    BAD_SYMBOLIC_APPROX = OUT / "one_step_gd_bad_symbolic_coefficient_approximate_gram.json"
    BAD_SYMBOLIC_REPORT = OUT / "one_step_gd_bad_symbolic_coefficient_adapter_report.json"
    BAD_SYMBOLIC_MANIFEST = OUT / "one_step_gd_bad_symbolic_coefficient_adapter_manifest.json"
    BAD_SYMBOLIC_LEAN = (
        ROOT
        / "LeanPEP"
        / "Imported"
        / "PEPitOneStepBadSymbolicCoefficientAdapter.lean"
    )
    RAW = OUT / "one_step_gd_raw.json"
    RECONSTRUCTED = OUT / "one_step_gd_reconstructed.json"

    GOOD_NS = "LeanPEP.Imported.PEPitOneStepAdapter"
    BAD_NS = "LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter"
    BAD_SYMBOLIC_NS = "LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter"
    COMPARISON_NS = "LeanPEP.Imported.PEPitOneStepApproxComparison"

    def load(self, path: Path | None = None) -> dict:
        return copy.deepcopy(dict(adapter.load_json(path or self.SOURCE)))

    def adapt(self, raw: dict | None = None) -> tuple[dict, dict, adapter.SourceArtifact]:
        source = adapter.parse_source(copy.deepcopy(raw or self.load()))
        approximate, report = adapter.adapt_source(source)
        return dict(approximate), dict(report), source

    def prepare_tracks(self, approximate: dict) -> prep.PreparedArtifacts:
        return prep.prepare_artifacts(
            approximate,
            raw_namespace="LeanPEP.Imported.TestPEPitRaw",
            reconstructed_namespace="LeanPEP.Imported.TestPEPitReconstructed",
            comparison_namespace="LeanPEP.Imported.TestPEPitComparison",
        )

    def run_cli(
        self,
        source: Path,
        directory: Path,
        namespace: str,
        *,
        comparison: bool = True,
        check: bool = False,
    ) -> tuple[Path, Path, Path, Path, subprocess.CompletedProcess[str]]:
        approx = directory / "approx.json"
        report = directory / "report.json"
        manifest = directory / "manifest.json"
        lean = directory / "Generated.lean"
        command = [
            sys.executable,
            str(TOOLS_DIR / "adapt_pepit_one_step.py"),
            str(source),
            "--approximate-gram",
            str(approx),
            "--report",
            str(report),
            "--manifest",
            str(manifest),
            "--lean-metadata",
            str(lean),
            "--lean-namespace",
            namespace,
        ]
        if comparison:
            command += ["--comparison-import", self.COMPARISON_NS]
        if check:
            command.append("--check")
        result = subprocess.run(command, text=True, capture_output=True, check=False)
        return approx, report, manifest, lean, result

    def test_committed_generated_files_are_current(self) -> None:
        for source, approx, report, manifest, lean, namespace in (
            (
                self.SOURCE,
                self.APPROX,
                self.REPORT,
                self.MANIFEST,
                self.LEAN,
                self.GOOD_NS,
            ),
            (
                self.BAD_ORDER_SOURCE,
                self.BAD_APPROX,
                self.BAD_REPORT,
                self.BAD_MANIFEST,
                self.BAD_LEAN,
                self.BAD_NS,
            ),
            (
                self.BAD_SYMBOLIC_SOURCE,
                self.BAD_SYMBOLIC_APPROX,
                self.BAD_SYMBOLIC_REPORT,
                self.BAD_SYMBOLIC_MANIFEST,
                self.BAD_SYMBOLIC_LEAN,
                self.BAD_SYMBOLIC_NS,
            ),
        ):
            command = [
                sys.executable,
                str(TOOLS_DIR / "adapt_pepit_one_step.py"),
                str(source),
                "--approximate-gram",
                str(approx),
                "--report",
                str(report),
                "--manifest",
                str(manifest),
                "--lean-metadata",
                str(lean),
                "--lean-namespace",
                namespace,
                "--comparison-import",
                self.COMPARISON_NS,
                "--check",
            ]
            subprocess.run(command, check=True)

    def test_good_source_is_accepted_and_fixture_is_not_a_live_claim(self) -> None:
        _, report, source = self.adapt()
        self.assertTrue(report["accepted"])
        self.assertEqual(report["mismatches"], [])
        self.assertEqual(source.capture_mode, "deterministic_regression_fixture")
        self.assertFalse(report["live_solver_claim"])

    def test_bad_constraint_order_is_rejected_at_formulation_level(self) -> None:
        _, report, _ = self.adapt(self.load(self.BAD_ORDER_SOURCE))
        self.assertFalse(report["accepted"])
        fields = {item["field"] for item in report["mismatches"]}
        self.assertIn("problem.constraint_order", fields)
        self.assertIn("problem.model_fingerprint.declared", fields)
        self.assertIn("problem.model_fingerprint.computed", fields)

    def test_bad_order_preserves_the_same_mathematical_numerical_payload(self) -> None:
        good, _, _ = self.adapt()
        bad, _, _ = self.adapt(self.load(self.BAD_ORDER_SOURCE))
        for field in ("declared", "ordering", "policy", "expect", "model", "primal"):
            self.assertEqual(good[field], bad[field])
        self.assertEqual(good["upper"], bad["upper"])
        self.assertNotEqual(good["source"], bad["source"])

    def test_bad_symbolic_coefficient_is_rejected_even_with_expected_declared_fingerprint(self) -> None:
        raw = self.load(self.BAD_SYMBOLIC_SOURCE)
        self.assertEqual(raw["problem"]["model_fingerprint"], adapter.expected_model_fingerprint())
        approximate, report, _ = self.adapt(raw)
        self.assertFalse(report["accepted"])
        fields = {item["field"] for item in report["mismatches"]}
        self.assertIn("problem.constraints[smooth_convexity:star:x0]", fields)
        self.assertIn("problem.model_fingerprint.computed", fields)
        self.assertNotIn("problem.model_fingerprint.declared", fields)
        good, _, _ = self.adapt()
        for field in ("declared", "ordering", "policy", "expect", "model", "primal", "upper"):
            self.assertEqual(approximate[field], good[field])
        self.assertNotEqual(approximate["source"], good["source"])

    def test_generated_lean_carries_typed_symbolic_arrays_and_basis_transform(self) -> None:
        source = adapter.parse_source(self.load())
        approximate, report = adapter.adapt_source(source)
        manifest = adapter.build_manifest(source, report)
        text = adapter.render_adapter_lean(
            source, report, manifest, self.GOOD_NS,
            comparison_import=self.COMPARISON_NS,
        )
        self.assertIn("def symbolicSourceQ", text)
        self.assertIn("pointDecomposition :=", text)
        self.assertIn("constraints :=", text)
        self.assertIn("nativeToCentered :=", text)
        self.assertIn("symbolic := symbolicSourceQ", text)

    def test_generated_lean_uses_valid_nested_record_layout(self) -> None:
        source = adapter.parse_source(self.load())
        _, report = adapter.adapt_source(source)
        manifest = adapter.build_manifest(source, report)
        text = adapter.render_adapter_lean(
            source, report, manifest, self.GOOD_NS,
            comparison_import=self.COMPARISON_NS,
        )
        self.assertEqual(
            text.count("          expr :=\n            { constCoeff :="),
            len(source.constraints),
        )
        self.assertNotIn("          expr := { constCoeff :=", text)

    def test_adapter_reuses_approximate_gram_schema_unchanged(self) -> None:
        approximate, _, _ = self.adapt()
        self.assertEqual(approximate["schema_version"], 1)
        tracks = self.prepare_tracks(approximate)
        self.assertEqual(tracks.raw_exact["schema_version"], 1)
        self.assertEqual(tracks.reconstructed_exact["schema_version"], 1)

    def test_raw_and_reconstructed_outcomes_are_distinct(self) -> None:
        approximate, _, _ = self.adapt()
        tracks = self.prepare_tracks(approximate)
        self.assertNotEqual(tracks.raw_exact, tracks.reconstructed_exact)
        reconstructed = exact.parse_bundle(tracks.reconstructed_exact)
        self.assertEqual(reconstructed.primal.value[2] - reconstructed.primal.value[0], Fraction(1, 6))
        self.assertEqual(reconstructed.upper.bound, Fraction(1, 6))

    def test_committed_raw_and_reconstructed_match_adapter_payload(self) -> None:
        approximate, _, _ = self.adapt()
        tracks = self.prepare_tracks(approximate)
        self.assertEqual(exact.load_json(self.RAW), tracks.raw_exact)
        self.assertEqual(exact.load_json(self.RECONSTRUCTED), tracks.reconstructed_exact)

    def test_factorization_hints_are_exact_for_the_source_matrices(self) -> None:
        _, report, _ = self.adapt()
        checks = report["factorization_hint_checks"]
        self.assertTrue(checks["primal_exact_for_source_matrix"])
        self.assertTrue(checks["dual_exact_for_source_matrix"])

    def test_native_to_centered_transform_has_expected_entries(self) -> None:
        approximate, report, _ = self.adapt()
        gram = approximate["primal"]["gram"]
        self.assertEqual(gram[0][0], "1")
        self.assertEqual(gram[0][1], "0.3333333333")
        self.assertEqual(gram[2][2], "0.11111111108888888889")
        self.assertEqual(
            report["target"]["gram_basis_order"],
            ["x0_minus_xstar", "g0", "g1"],
        )

    def test_json_float_is_rejected(self) -> None:
        raw = self.load()
        raw["solver_output"]["primal_gram"][0][0] = 4.0
        with self.assertRaisesRegex(adapter.AdapterFormatError, "expected a string"):
            adapter.parse_source(raw)

    def test_duplicate_keys_are_rejected(self) -> None:
        with self.assertRaisesRegex(exact.ImportFormatError, "duplicate key"):
            json.loads(
                '{"schema_version": 1, "schema_version": 1}',
                object_pairs_hook=exact.reject_duplicate_pairs,
            )

    def test_unknown_field_is_rejected(self) -> None:
        raw = self.load()
        raw["producer"]["unverified_magic"] = "yes"
        with self.assertRaisesRegex(adapter.AdapterFormatError, "unknown field"):
            adapter.parse_source(raw)

    def test_invalid_capture_mode_is_rejected(self) -> None:
        raw = self.load()
        raw["producer"]["capture_mode"] = "pretend_live"
        with self.assertRaisesRegex(adapter.AdapterFormatError, "live_pepit"):
            adapter.parse_source(raw)

    def test_wrong_matrix_shape_is_rejected(self) -> None:
        raw = self.load()
        raw["solver_output"]["dual_residual"].pop()
        with self.assertRaisesRegex(adapter.AdapterFormatError, "exactly 4 rows"):
            adapter.parse_source(raw)

    def test_symbolic_constraint_coefficient_change_is_reported(self) -> None:
        raw = self.load()
        raw["problem"]["constraints"][1]["expr"]["value_coeff"][0] = "-0.9"
        _, report, _ = self.adapt(raw)
        fields = {item["field"] for item in report["mismatches"]}
        self.assertIn("problem.constraints[smooth_convexity:star:x0]", fields)
        self.assertIn("problem.model_fingerprint.computed", fields)

    def test_scientific_notation_is_interpreted_exactly(self) -> None:
        raw = self.load()
        raw["solver_output"]["dual_objective"] = "1.666666667e-1"
        _, _, source = self.adapt(raw)
        self.assertEqual(source.dual_objective, Fraction(1666666667, 10_000_000_000))

    def test_hash_chain_and_rendered_provenance_are_exact(self) -> None:
        source_obj = self.load()
        source = adapter.parse_source(source_obj)
        approximate, report = adapter.adapt_source(source)
        manifest = json.loads(self.MANIFEST.read_text(encoding="utf-8"))
        self.assertEqual(source.source_sha256, base.canonical_json_sha256(source_obj))
        self.assertEqual(
            report["adapted_approximate_gram_sha256"],
            base.canonical_json_sha256(approximate),
        )
        self.assertEqual(
            manifest["hashes"]["adapter_report_sha256"],
            base.canonical_json_sha256(report),
        )
        lean = self.LEAN.read_text(encoding="utf-8")
        self.assertIn(source.source_sha256, lean)
        self.assertIn(manifest["hashes"]["adapter_report_sha256"], lean)

    def test_rendering_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            out_a = self.run_cli(self.SOURCE, Path(a), "LeanPEP.Imported.TempPEPitA")
            out_b = self.run_cli(self.SOURCE, Path(b), "LeanPEP.Imported.TempPEPitA")
            self.assertEqual(out_a[-1].returncode, 0, out_a[-1].stderr)
            self.assertEqual(out_b[-1].returncode, 0, out_b[-1].stderr)
            for pa, pb in zip(out_a[:4], out_b[:4], strict=True):
                self.assertEqual(pa.read_bytes(), pb.read_bytes())

    def test_check_mode_detects_stale_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            outputs = self.run_cli(self.SOURCE, directory, "LeanPEP.Imported.TempPEPit")
            self.assertEqual(outputs[-1].returncode, 0, outputs[-1].stderr)
            outputs[0].write_text("stale\n", encoding="utf-8")
            checked = self.run_cli(
                self.SOURCE,
                directory,
                "LeanPEP.Imported.TempPEPit",
                check=True,
            )
            self.assertEqual(checked[-1].returncode, 2)
            self.assertIn("stale", checked[-1].stderr)

    def test_source_hash_changes_when_constraint_order_changes(self) -> None:
        good = adapter.parse_source(self.load())
        bad = adapter.parse_source(self.load(self.BAD_ORDER_SOURCE))
        self.assertNotEqual(good.source_sha256, bad.source_sha256)
        self.assertNotEqual(good.declared_model_fingerprint, bad.declared_model_fingerprint)


    def test_factor_hints_do_not_define_formulation_acceptance(self) -> None:
        raw = self.load()
        raw["factorization_hints"]["primal_gram"]["factors"][0]["weight"] = "0.9"
        _, report, _ = self.adapt(raw)
        self.assertTrue(report["accepted"])
        self.assertFalse(
            report["factorization_hint_checks"]["primal_exact_for_source_matrix"]
        )

    def test_live_exporter_help_and_commit_pin_without_pepit(self) -> None:
        help_proc = subprocess.run(
            [sys.executable, str(TOOLS_DIR / "export_pepit_one_step_artifact.py"), "--help"],
            text=True, capture_output=True, check=False,
        )
        self.assertEqual(help_proc.returncode, 0)
        self.assertIn("pepit-sdp-artifact-v1", help_proc.stdout)
        with tempfile.TemporaryDirectory() as tmp:
            bad_proc = subprocess.run(
                [
                    sys.executable,
                    str(TOOLS_DIR / "export_pepit_one_step_artifact.py"),
                    str(Path(tmp) / "unused.json"),
                    "--pepit-commit",
                    "wrong-commit",
                ],
                text=True, capture_output=True, check=False,
            )
        self.assertEqual(bad_proc.returncode, 2)
        self.assertIn(adapter.PEPIT_COMMIT, bad_proc.stderr)


if __name__ == "__main__":
    unittest.main()
