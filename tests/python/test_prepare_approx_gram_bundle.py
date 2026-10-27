#!/usr/bin/env python3
"""Tests for the approximate Gram raw/reconstruction preprocessing pipeline."""

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

import import_exact_bundle as base  # noqa: E402
import import_exact_gram_bundle as exact  # noqa: E402
import prepare_approx_gram_bundle as prep  # noqa: E402


class PrepareApproxGramBundleTests(unittest.TestCase):
    SOURCE = ROOT / "data/fixtures" / "gram_approximate" / "one_step_near_exact.json"
    RAW = ROOT / "data/fixtures" / "gram_generated" / "one_step_near_exact_raw.json"
    RECONSTRUCTED = (
        ROOT / "data/fixtures" / "gram_generated" / "one_step_near_exact_reconstructed.json"
    )
    REPORT = (
        ROOT
        / "data/fixtures"
        / "gram_generated"
        / "one_step_near_exact_reconstruction_report.json"
    )
    MANIFEST = (
        ROOT
        / "data/fixtures"
        / "gram_generated"
        / "one_step_near_exact_comparison_manifest.json"
    )
    COMPARISON = ROOT / "LeanPEP" / "Imported" / "GramOneStepApproxComparison.lean"
    RAW_LEAN = ROOT / "LeanPEP" / "Imported" / "GramOneStepApproxRaw.lean"
    RECONSTRUCTED_LEAN = (
        ROOT / "LeanPEP" / "Imported" / "GramOneStepApproxReconstructed.lean"
    )

    RAW_NS = "LeanPEP.Imported.GramOneStepApproxRaw"
    RECONSTRUCTED_NS = "LeanPEP.Imported.GramOneStepApproxReconstructed"
    COMPARISON_NS = "LeanPEP.Imported.GramOneStepApproxComparison"

    def load_source(self) -> dict:
        return dict(prep.load_json(self.SOURCE))

    def prepare(self, raw: dict | None = None) -> prep.PreparedArtifacts:
        return prep.prepare_artifacts(
            copy.deepcopy(raw if raw is not None else self.load_source()),
            raw_namespace=self.RAW_NS,
            reconstructed_namespace=self.RECONSTRUCTED_NS,
            comparison_namespace=self.COMPARISON_NS,
        )

    def test_committed_generated_files_are_current(self) -> None:
        artifacts = self.prepare()
        expected = prep.rendered_outputs(artifacts)
        actual = (
            self.RAW.read_text(encoding="utf-8"),
            self.RECONSTRUCTED.read_text(encoding="utf-8"),
            self.REPORT.read_text(encoding="utf-8"),
            self.MANIFEST.read_text(encoding="utf-8"),
            self.COMPARISON.read_text(encoding="utf-8"),
        )
        self.assertEqual(actual, expected)

        raw_spec = exact.parse_bundle(exact.load_json(self.RAW))
        reconstructed_spec = exact.parse_bundle(exact.load_json(self.RECONSTRUCTED))
        self.assertEqual(
            self.RAW_LEAN.read_text(encoding="utf-8"),
            exact.render_module(raw_spec, self.RAW_NS),
        )
        self.assertEqual(
            self.RECONSTRUCTED_LEAN.read_text(encoding="utf-8"),
            exact.render_module(reconstructed_spec, self.RECONSTRUCTED_NS),
        )

    def test_candidate_json_float_is_rejected(self) -> None:
        raw = self.load_source()
        raw["primal"]["gram"][0][0] = 1.0
        with self.assertRaisesRegex(prep.ApproxFormatError, "expected a string"):
            prep.build_exact_tracks(raw)

    def test_policy_json_float_is_rejected(self) -> None:
        raw = self.load_source()
        raw["policy"]["max_abs_error"] = 1e-9
        with self.assertRaisesRegex(prep.ApproxFormatError, "expected a string"):
            prep.build_exact_tracks(raw)

    def test_nan_and_infinity_are_rejected(self) -> None:
        for bad in ("NaN", "Infinity", "-Infinity"):
            with self.subTest(value=bad):
                raw = self.load_source()
                raw["upper"]["dual_matrix"][0][0] = bad
                with self.assertRaisesRegex(
                    prep.ApproxFormatError, "finite base-10 decimal string"
                ):
                    prep.build_exact_tracks(raw)

    def test_duplicate_json_keys_are_rejected(self) -> None:
        with self.assertRaisesRegex(base.ImportFormatError, "duplicate key"):
            json.loads(
                '{"schema_version": 1, "schema_version": 1}',
                object_pairs_hook=base.reject_duplicate_pairs,
            )

    def test_unknown_fields_are_rejected(self) -> None:
        raw = self.load_source()
        raw["upper"]["dual_psd_matrix"] = raw["upper"]["dual_matrix"]
        with self.assertRaisesRegex(prep.ApproxFormatError, "unknown field"):
            prep.build_exact_tracks(raw)

    def test_duplicate_ordering_labels_are_rejected(self) -> None:
        raw = self.load_source()
        raw["ordering"]["gram_basis"][2] = "g0"
        with self.assertRaisesRegex(prep.ApproxFormatError, "labels must be unique"):
            prep.build_exact_tracks(raw)

    def test_wrong_vector_length_is_rejected(self) -> None:
        raw = self.load_source()
        raw["upper"]["dual_factor"]["factors"][0]["vector"].pop()
        with self.assertRaisesRegex(prep.ApproxFormatError, "exactly 3 entries"):
            prep.build_exact_tracks(raw)

    def test_out_of_range_indices_are_rejected(self) -> None:
        raw = self.load_source()
        raw["upper"]["interp_terms"][0]["j"] = 3
        with self.assertRaisesRegex(prep.ApproxFormatError, "outside 0..2"):
            prep.build_exact_tracks(raw)

    def test_scientific_notation_is_interpreted_exactly(self) -> None:
        raw = self.load_source()
        raw["upper"]["interp_terms"][0]["weight"] = "5e-1"
        artifacts = self.prepare(raw)
        self.assertEqual(
            artifacts.raw_exact["upper"]["interp_terms"][0]["weight"],
            {"num": 1, "den": 2},
        )

    def test_reconstruction_respects_denominator_and_error_bounds(self) -> None:
        artifacts = self.prepare()
        report = artifacts.report
        max_denominator = report["policy"]["max_denominator"]
        max_error_obj = report["policy"]["max_abs_error_exact"]
        max_error = Fraction(max_error_obj["num"], max_error_obj["den"])
        for entry in report["entries"]:
            reconstructed = entry["reconstructed"]
            error = entry["absolute_error"]
            self.assertLessEqual(reconstructed["den"], max_denominator)
            self.assertLessEqual(Fraction(error["num"], error["den"]), max_error)

    def test_too_small_error_bound_is_rejected_without_silent_repair(self) -> None:
        raw = self.load_source()
        raw["policy"]["max_abs_error"] = "1e-12"
        with self.assertRaisesRegex(prep.ApproxFormatError, "exceeds policy"):
            prep.build_exact_tracks(raw)

    def test_raw_and_reconstructed_semantics_are_distinct(self) -> None:
        artifacts = self.prepare()
        self.assertNotEqual(artifacts.raw_exact, artifacts.reconstructed_exact)
        exact_fixture = exact.load_json(
            ROOT / "data/fixtures" / "gram_external" / "one_step_exact.json"
        )
        for field in ("declared", "ordering", "model", "primal", "upper"):
            self.assertEqual(artifacts.reconstructed_exact[field], exact_fixture[field])

        raw_spec = exact.parse_bundle(artifacts.raw_exact)
        reconstructed_spec = exact.parse_bundle(artifacts.reconstructed_exact)
        raw_objective = raw_spec.primal.value[2] - raw_spec.primal.value[0]
        reconstructed_objective = (
            reconstructed_spec.primal.value[2] - reconstructed_spec.primal.value[0]
        )
        self.assertNotEqual(raw_objective, raw_spec.upper.bound)
        self.assertEqual(reconstructed_objective, reconstructed_spec.upper.bound)
        self.assertEqual(reconstructed_objective, Fraction(1, 6))

    def test_raw_track_has_exact_negative_slacks(self) -> None:
        spec = exact.parse_bundle(self.prepare().raw_exact)
        p = spec.point_count
        m = spec.gram_basis_count
        G = spec.primal.gram

        def inner(u: tuple[Fraction, ...], v: tuple[Fraction, ...]) -> Fraction:
            return sum(
                u[i] * G[i][j] * v[j]
                for i in range(m)
                for j in range(m)
            )

        violations: list[tuple[int, int, Fraction]] = []
        for i in range(p):
            for j in range(p):
                dx = tuple(
                    spec.model.position[i][k] - spec.model.position[j][k]
                    for k in range(m)
                )
                dg = tuple(
                    spec.model.gradient[i][k] - spec.model.gradient[j][k]
                    for k in range(m)
                )
                slack = (
                    spec.primal.value[i]
                    - spec.primal.value[j]
                    - inner(spec.model.gradient[j], dx)
                    - Fraction(1, 2) * inner(dg, dg)
                )
                if slack < 0:
                    violations.append((i, j, slack))
        self.assertEqual(
            violations,
            [
                (0, 1, Fraction(-8888888889, 200000000000000000000)),
                (0, 2, Fraction(-26666666667, 200000000000000000000)),
                (1, 2, Fraction(-8888888889, 100000000000000000000)),
            ],
        )

    def test_raw_factorizations_are_exact_for_the_raw_objects(self) -> None:
        spec = exact.parse_bundle(self.prepare().raw_exact)
        m = spec.gram_basis_count

        def factor_matrix(cert: exact.FactorCertSpec) -> tuple[tuple[Fraction, ...], ...]:
            result = [[Fraction(0) for _ in range(m)] for _ in range(m)]
            for factor in cert.factors:
                for i in range(m):
                    for j in range(m):
                        result[i][j] += (
                            factor.weight * factor.vector[i] * factor.vector[j]
                        )
            return tuple(tuple(row) for row in result)

        self.assertEqual(factor_matrix(spec.primal.gram_factor), spec.primal.gram)
        self.assertEqual(factor_matrix(spec.upper.dual_factor), spec.upper.dual_matrix)

    def test_hash_chain_is_exact_and_complete(self) -> None:
        raw = self.load_source()
        artifacts = self.prepare(raw)
        manifest = artifacts.manifest
        hashes = manifest["hashes"]
        self.assertEqual(hashes["source_sha256"], base.canonical_json_sha256(raw))
        self.assertEqual(
            hashes["raw_exact_sha256"],
            base.canonical_json_sha256(artifacts.raw_exact),
        )
        self.assertEqual(
            hashes["reconstructed_exact_sha256"],
            base.canonical_json_sha256(artifacts.reconstructed_exact),
        )
        self.assertEqual(
            hashes["reconstruction_report_sha256"],
            base.canonical_json_sha256(artifacts.report),
        )
        self.assertIn(
            base.canonical_json_sha256(artifacts.manifest),
            artifacts.comparison_lean,
        )

    def test_report_covers_all_gram_certificate_layers(self) -> None:
        paths = {entry["path"] for entry in self.prepare().report["entries"]}
        required = {
            "$.model.position[0][0]",
            "$.model.assumptions[0].expr.gram_coeff[0][0]",
            "$.primal.gram[0][1]",
            "$.primal.gram_factor.factors[0].vector[1]",
            "$.upper.bound",
            "$.upper.interp_terms[0].weight",
            "$.upper.dual_matrix[0][0]",
            "$.upper.dual_factor.factors[2].vector[0]",
        }
        self.assertTrue(required.issubset(paths))
        self.assertEqual(self.prepare().report["entry_count"], 86)

    def test_exact_gram_schema_is_reused_unchanged(self) -> None:
        artifacts = self.prepare()
        expected_keys = {
            "schema_version",
            "source",
            "declared",
            "ordering",
            "model",
            "primal",
            "upper",
            "expect",
        }
        for bundle in (artifacts.raw_exact, artifacts.reconstructed_exact):
            self.assertEqual(set(bundle), expected_keys)
            self.assertNotIn("policy", bundle)
            exact.parse_bundle(bundle)

    def test_rendering_is_deterministic(self) -> None:
        rendered1 = prep.rendered_outputs(self.prepare())
        rendered2 = prep.rendered_outputs(self.prepare())
        self.assertEqual(rendered1, rendered2)

    def test_check_mode_detects_stale_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            raw_path = tmp / "raw.json"
            reconstructed_path = tmp / "reconstructed.json"
            report_path = tmp / "report.json"
            manifest_path = tmp / "manifest.json"
            comparison_path = tmp / "Comparison.lean"
            args = [
                sys.executable,
                str(TOOLS_DIR / "prepare_approx_gram_bundle.py"),
                str(self.SOURCE),
                "--raw-exact",
                str(raw_path),
                "--reconstructed-exact",
                str(reconstructed_path),
                "--report",
                str(report_path),
                "--manifest",
                str(manifest_path),
                "--comparison-lean",
                str(comparison_path),
                "--raw-namespace",
                self.RAW_NS,
                "--reconstructed-namespace",
                self.RECONSTRUCTED_NS,
                "--comparison-namespace",
                self.COMPARISON_NS,
            ]
            generated = subprocess.run(args, text=True, capture_output=True, check=False)
            self.assertEqual(generated.returncode, 0, generated.stderr)
            report_path.write_text("stale\n", encoding="utf-8")
            checked = subprocess.run(
                args + ["--check"], text=True, capture_output=True, check=False
            )
            self.assertEqual(checked.returncode, 2)
            self.assertIn("stale", checked.stderr)


if __name__ == "__main__":
    unittest.main()
