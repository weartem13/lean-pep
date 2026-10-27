#!/usr/bin/env python3
"""Unit, golden, and exact-arithmetic tests for Gram bundle import v1."""

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

import import_exact_gram_bundle as importer  # noqa: E402


class ImportExactGramBundleTests(unittest.TestCase):
    CASES = (
        (
            "one_step_exact.json",
            "LeanPEP.Imported.GramOneStepExact",
            "GramOneStepExact.lean",
        ),
        (
            "one_step_bad_metadata.json",
            "LeanPEP.Imported.GramOneStepBadMetadata",
            "GramOneStepBadMetadata.lean",
        ),
        (
            "one_step_bad_primal.json",
            "LeanPEP.Imported.GramOneStepBadPrimal",
            "GramOneStepBadPrimal.lean",
        ),
        (
            "one_step_bad_primal_factor.json",
            "LeanPEP.Imported.GramOneStepBadPrimalFactor",
            "GramOneStepBadPrimalFactor.lean",
        ),
        (
            "one_step_bad_upper.json",
            "LeanPEP.Imported.GramOneStepBadUpper",
            "GramOneStepBadUpper.lean",
        ),
    )

    def load_raw(self, filename: str = "one_step_exact.json") -> dict:
        path = ROOT / "data/fixtures" / "gram_external" / filename
        return dict(importer.load_json(path))

    def test_committed_generated_files_are_current(self) -> None:
        for fixture, namespace, lean_name in self.CASES:
            with self.subTest(fixture=fixture):
                spec = importer.parse_bundle(self.load_raw(fixture))
                expected = importer.render_module(spec, namespace)
                actual = (ROOT / "LeanPEP" / "Imported" / lean_name).read_text(
                    encoding="utf-8"
                )
                self.assertEqual(actual, expected)

    def test_exact_rationals_reject_json_float(self) -> None:
        raw = self.load_raw()
        raw["primal"]["gram"][0][0]["num"] = 1.0
        with self.assertRaisesRegex(
            importer.ImportFormatError, "JSON floats are never accepted"
        ):
            importer.parse_bundle(raw)

    def test_nonpositive_denominator_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["bound"]["den"] = 0
        with self.assertRaisesRegex(importer.ImportFormatError, "integer >= 1"):
            importer.parse_bundle(raw)

    def test_duplicate_json_keys_are_rejected(self) -> None:
        with self.assertRaisesRegex(importer.ImportFormatError, "duplicate key"):
            json.loads(
                '{"schema_version": 1, "schema_version": 1}',
                object_pairs_hook=importer.reject_duplicate_pairs,
            )

    def test_unknown_field_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["dual_psd_matrix"] = raw["upper"]["dual_matrix"]
        with self.assertRaisesRegex(importer.ImportFormatError, "unknown field"):
            importer.parse_bundle(raw)

    def test_duplicate_ordering_labels_are_rejected(self) -> None:
        raw = self.load_raw()
        raw["ordering"]["gram_basis"][2] = "g0"
        with self.assertRaisesRegex(importer.ImportFormatError, "labels must be unique"):
            importer.parse_bundle(raw)

    def test_duplicate_assumption_names_are_rejected(self) -> None:
        raw = self.load_raw()
        raw["model"]["assumptions"].append(
            copy.deepcopy(raw["model"]["assumptions"][0])
        )
        with self.assertRaisesRegex(importer.ImportFormatError, "duplicate assumption"):
            importer.parse_bundle(raw)

    def test_wrong_model_vector_length_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["model"]["position"][0].pop()
        with self.assertRaisesRegex(importer.ImportFormatError, "exactly 3 entries"):
            importer.parse_bundle(raw)

    def test_wrong_gram_matrix_shape_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["primal"]["gram"].pop()
        with self.assertRaisesRegex(importer.ImportFormatError, "exactly 3 rows"):
            importer.parse_bundle(raw)

    def test_wrong_factor_vector_length_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["primal"]["gram_factor"]["factors"][0]["vector"].pop()
        with self.assertRaisesRegex(importer.ImportFormatError, "exactly 3 entries"):
            importer.parse_bundle(raw)

    def test_out_of_range_interpolation_index_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["interp_terms"][0]["j"] = 3
        with self.assertRaisesRegex(importer.ImportFormatError, "outside 0..2"):
            importer.parse_bundle(raw)

    def test_out_of_range_assumption_index_is_rejected(self) -> None:
        raw = self.load_raw()
        raw["upper"]["assumption_terms"][0]["index"] = 1
        with self.assertRaisesRegex(importer.ImportFormatError, "outside 0..0"):
            importer.parse_bundle(raw)

    def test_metadata_mismatch_is_preserved_for_lean_auditing(self) -> None:
        spec = importer.parse_bundle(self.load_raw("one_step_bad_metadata.json"))
        self.assertEqual(spec.declared.ordered_pair_count, 8)
        rendered = importer.render_module(
            spec, "LeanPEP.Imported.GramOneStepBadMetadata"
        )
        self.assertIn("declaredOrderedPairCount := 8", rendered)
        self.assertIn("checkExactGramBundleQ bundleQ = false", rendered)

    def test_rendering_is_deterministic(self) -> None:
        raw = self.load_raw()
        spec1 = importer.parse_bundle(copy.deepcopy(raw))
        spec2 = importer.parse_bundle(copy.deepcopy(raw))
        self.assertEqual(
            importer.render_module(spec1, "LeanPEP.Imported.DeterministicGram"),
            importer.render_module(spec2, "LeanPEP.Imported.DeterministicGram"),
        )

    def test_source_hash_is_canonical_and_rendered(self) -> None:
        raw = self.load_raw()
        spec = importer.parse_bundle(copy.deepcopy(raw))
        expected = importer.canonical_json_sha256(raw)
        self.assertEqual(spec.source_sha256, expected)
        rendered = importer.render_module(spec, "LeanPEP.Imported.HashGram")
        self.assertIn(expected, rendered)

    def test_check_mode_detects_stale_output(self) -> None:
        input_path = ROOT / "data/fixtures" / "gram_external" / "one_step_exact.json"
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "Generated.lean"
            output.write_text("stale\n", encoding="utf-8")
            proc = subprocess.run(
                [
                    sys.executable,
                    str(TOOLS_DIR / "import_exact_gram_bundle.py"),
                    str(input_path),
                    str(output),
                    "--namespace",
                    "LeanPEP.Imported.CheckModeGram",
                    "--check",
                ],
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 2)
            self.assertIn("stale", proc.stderr)

    def test_accepted_fixture_has_exact_closed_loop_arithmetic(self) -> None:
        spec = importer.parse_bundle(self.load_raw())
        p = spec.point_count
        m = spec.gram_basis_count
        G = spec.primal.gram

        def inner(u: tuple[Fraction, ...], v: tuple[Fraction, ...]) -> Fraction:
            return sum(
                u[i] * G[i][j] * v[j]
                for i in range(m)
                for j in range(m)
            )

        slacks: list[Fraction] = []
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
                slacks.append(
                    spec.primal.value[i]
                    - spec.primal.value[j]
                    - inner(spec.model.gradient[j], dx)
                    - Fraction(1, 2) * inner(dg, dg)
                )
        self.assertEqual(len(slacks), 9)
        self.assertGreaterEqual(min(slacks), 0)

        def factor_matrix(cert: importer.FactorCertSpec) -> list[list[Fraction]]:
            result = [[Fraction(0) for _ in range(m)] for _ in range(m)]
            for factor in cert.factors:
                for i in range(m):
                    for j in range(m):
                        result[i][j] += (
                            factor.weight * factor.vector[i] * factor.vector[j]
                        )
            return result

        self.assertEqual(factor_matrix(spec.primal.gram_factor), [list(r) for r in G])
        self.assertEqual(
            factor_matrix(spec.upper.dual_factor),
            [list(r) for r in spec.upper.dual_matrix],
        )

        def eval_linear(expr: importer.LinearExprSpec) -> Fraction:
            return (
                expr.const
                + sum(
                    expr.value_coeff[i] * spec.primal.value[i]
                    for i in range(p)
                )
                + sum(
                    expr.gram_coeff[i][j] * G[i][j]
                    for i in range(m)
                    for j in range(m)
                )
            )

        self.assertEqual(eval_linear(spec.model.assumptions[0].expr), 0)
        self.assertEqual(eval_linear(spec.upper.objective), spec.upper.bound)
        self.assertEqual(spec.upper.bound, Fraction(1, 6))


if __name__ == "__main__":
    unittest.main()
