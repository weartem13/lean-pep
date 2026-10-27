#!/usr/bin/env python3
"""Prepare exact raw and reconstructed candidates from approximate PEP JSON.

The input format keeps every candidate decimal as a JSON string.  This script
interprets each string exactly through ``Decimal``/``Fraction`` and emits two
unchanged schema-v1 exact bundles:

* a raw bundle containing the exact base-10 values from the source; and
* a reconstructed bundle produced by an explicit denominator/error policy.

It also emits a per-entry reconstruction report, a hash manifest, and a small
Lean comparison module.  The script is deliberately untrusted: both exact
bundles are subsequently checked by the existing Lean exact-bundle kernel.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

import import_exact_bundle as exact

GENERATOR_VERSION = "v0.7.0"
APPROX_SCHEMA_VERSION = 1
REPORT_SCHEMA_VERSION = 1
MANIFEST_SCHEMA_VERSION = 1
RECONSTRUCTION_METHOD = "limit_denominator"
FD = "LeanPEP.Toy.FiniteGD"

# Finite base-10 strings only.  Integers and scientific notation are valid;
# NaN/Infinity and surrounding whitespace are not.
_DECIMAL_STRING = re.compile(
    r"^[+-]?(?:(?:[0-9]+(?:\.[0-9]*)?)|(?:\.[0-9]+))(?:[eE][+-]?[0-9]+)?$"
)


class ApproxFormatError(ValueError):
    """Raised when approximate input or reconstruction policy is invalid."""


def fail(path: str, message: str) -> NoReturn:
    raise ApproxFormatError(f"{path}: {message}")


@dataclass(frozen=True)
class ReconstructionPolicy:
    method: str
    max_denominator: int
    max_abs_error_source: str
    max_abs_error: Fraction


@dataclass(frozen=True)
class ReconstructionEntry:
    path: str
    source: str
    source_exact: Fraction
    reconstructed: Fraction
    delta: Fraction
    absolute_error: Fraction


@dataclass(frozen=True)
class PreparedArtifacts:
    raw_exact: Mapping[str, Any]
    reconstructed_exact: Mapping[str, Any]
    report: Mapping[str, Any]
    manifest: Mapping[str, Any]
    comparison_lean: str


@dataclass(frozen=True)
class OutputPaths:
    raw_exact: Path
    reconstructed_exact: Path
    report: Path
    manifest: Path
    comparison_lean: Path


def require_object(value: Any, path: str) -> Mapping[str, Any]:
    try:
        return exact.require_object(value, path)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def require_array(value: Any, path: str) -> Sequence[Any]:
    try:
        return exact.require_array(value, path)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def require_string(value: Any, path: str) -> str:
    try:
        return exact.require_string(value, path)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def require_int(value: Any, path: str, *, minimum: int | None = None) -> int:
    try:
        return exact.require_int(value, path, minimum=minimum)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def check_keys(
    obj: Mapping[str, Any],
    path: str,
    *,
    required: Sequence[str],
    optional: Sequence[str] = (),
) -> None:
    try:
        exact.check_keys(obj, path, required=required, optional=optional)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def parse_decimal_string(value: Any, path: str) -> tuple[str, Fraction]:
    """Parse one finite decimal string without any binary-float conversion."""

    source = require_string(value, path)
    if source != source.strip() or not _DECIMAL_STRING.fullmatch(source):
        fail(
            path,
            "expected a finite base-10 decimal string; NaN/Infinity and JSON numbers are rejected",
        )
    try:
        decimal = Decimal(source)
    except InvalidOperation as exc:
        fail(path, f"invalid decimal string {source!r}")
    if not decimal.is_finite():
        fail(path, "NaN and Infinity are not accepted")
    # Fraction(Decimal) uses the exact finite base-10 value represented by the
    # Decimal object.  No Python float is constructed at any point.
    return source, Fraction(decimal)


def rational_json(value: Fraction) -> dict[str, int]:
    return {"num": value.numerator, "den": value.denominator}


def canonical_sha256(value: Mapping[str, Any]) -> str:
    return exact.canonical_json_sha256(value)


def parse_policy(value: Any, path: str = "$.policy") -> ReconstructionPolicy:
    obj = require_object(value, path)
    check_keys(
        obj,
        path,
        required=("method", "max_denominator", "max_abs_error"),
    )
    method = require_string(obj["method"], f"{path}.method")
    if method != RECONSTRUCTION_METHOD:
        fail(
            f"{path}.method",
            f"unsupported method {method!r}; expected {RECONSTRUCTION_METHOD!r}",
        )
    max_denominator = require_int(
        obj["max_denominator"], f"{path}.max_denominator", minimum=1
    )
    error_source, max_abs_error = parse_decimal_string(
        obj["max_abs_error"], f"{path}.max_abs_error"
    )
    if max_abs_error < 0:
        fail(f"{path}.max_abs_error", "must be nonnegative")
    return ReconstructionPolicy(
        method=method,
        max_denominator=max_denominator,
        max_abs_error_source=error_source,
        max_abs_error=max_abs_error,
    )


def parse_expect(value: Any, path: str = "$.expect") -> tuple[str, str]:
    if value is None:
        return ("unchecked", "unchecked")
    obj = require_object(value, path)
    check_keys(obj, path, required=("raw", "reconstructed"))
    raw = require_string(obj["raw"], f"{path}.raw")
    reconstructed = require_string(obj["reconstructed"], f"{path}.reconstructed")
    allowed = {"accepted", "rejected", "unchecked"}
    if raw not in allowed:
        fail(f"{path}.raw", "expected 'accepted', 'rejected', or 'unchecked'")
    if reconstructed not in allowed:
        fail(
            f"{path}.reconstructed",
            "expected 'accepted', 'rejected', or 'unchecked'",
        )
    return raw, reconstructed


class CandidateConverter:
    """Convert all candidate decimals while recording exact reconstruction data."""

    def __init__(self, policy: ReconstructionPolicy):
        self.policy = policy
        self.entries: list[ReconstructionEntry] = []

    def decimal(self, value: Any, path: str) -> tuple[dict[str, int], dict[str, int]]:
        source, source_exact = parse_decimal_string(value, path)
        reconstructed = source_exact.limit_denominator(self.policy.max_denominator)
        delta = reconstructed - source_exact
        absolute_error = abs(delta)
        if reconstructed.denominator > self.policy.max_denominator:
            fail(
                path,
                "internal reconstruction error: denominator exceeds configured bound",
            )
        if absolute_error > self.policy.max_abs_error:
            fail(
                path,
                "reconstruction error "
                f"{absolute_error.numerator}/{absolute_error.denominator} exceeds "
                "policy max_abs_error "
                f"{self.policy.max_abs_error.numerator}/{self.policy.max_abs_error.denominator}",
            )
        self.entries.append(
            ReconstructionEntry(
                path=path,
                source=source,
                source_exact=source_exact,
                reconstructed=reconstructed,
                delta=delta,
                absolute_error=absolute_error,
            )
        )
        return rational_json(source_exact), rational_json(reconstructed)

    def vector(
        self, value: Any, path: str, expected_length: int
    ) -> tuple[list[dict[str, int]], list[dict[str, int]]]:
        items = require_array(value, path)
        if len(items) != expected_length:
            fail(path, f"expected exactly {expected_length} entries, got {len(items)}")
        raw: list[dict[str, int]] = []
        reconstructed: list[dict[str, int]] = []
        for index, item in enumerate(items):
            raw_item, reconstructed_item = self.decimal(item, f"{path}[{index}]")
            raw.append(raw_item)
            reconstructed.append(reconstructed_item)
        return raw, reconstructed


def point_json(value: Any, path: str, steps: int) -> Mapping[str, Any]:
    try:
        point = exact.parse_point(value, path, steps)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc
    if point.kind == "star":
        return {"kind": "star"}
    assert point.index is not None
    return {"kind": "iter", "index": point.index}


def build_exact_tracks(
    raw: Any,
) -> tuple[
    Mapping[str, Any],
    Mapping[str, Any],
    ReconstructionPolicy,
    tuple[ReconstructionEntry, ...],
    str,
    str,
]:
    """Strictly parse approximate input and build the two exact schema-v1 tracks."""

    obj = require_object(raw, "$")
    check_keys(
        obj,
        "$",
        required=(
            "schema_version",
            "source",
            "steps",
            "declared_point_count",
            "declared_constraint_count",
            "policy",
            "primal",
            "upper",
        ),
        optional=("expect",),
    )
    schema_version = require_int(obj["schema_version"], "$.schema_version")
    if schema_version != APPROX_SCHEMA_VERSION:
        fail(
            "$.schema_version",
            f"unsupported schema version {schema_version}; expected {APPROX_SCHEMA_VERSION}",
        )
    source = require_string(obj["source"], "$.source")
    if not source:
        fail("$.source", "must not be empty")
    steps = require_int(obj["steps"], "$.steps", minimum=0)
    point_count = require_int(
        obj["declared_point_count"], "$.declared_point_count", minimum=0
    )
    constraint_count = require_int(
        obj["declared_constraint_count"],
        "$.declared_constraint_count",
        minimum=0,
    )
    policy = parse_policy(obj["policy"])
    raw_expect, reconstructed_expect = parse_expect(obj.get("expect"))
    converter = CandidateConverter(policy)

    primal_obj = require_object(obj["primal"], "$.primal")
    check_keys(primal_obj, "$.primal", required=("grad", "value"))
    raw_grad, reconstructed_grad = converter.vector(
        primal_obj["grad"], "$.primal.grad", steps + 1
    )
    raw_value, reconstructed_value = converter.vector(
        primal_obj["value"], "$.primal.value", steps + 1
    )

    upper_obj = require_object(obj["upper"], "$.upper")
    check_keys(
        upper_obj,
        "$.upper",
        required=("bound", "objective", "interp_terms", "square_terms"),
    )
    raw_bound, reconstructed_bound = converter.decimal(
        upper_obj["bound"], "$.upper.bound"
    )
    objective = require_int(
        upper_obj["objective"], "$.upper.objective", minimum=0
    )
    if objective > steps:
        fail(
            "$.upper.objective",
            f"objective index {objective} is outside 0..{steps}",
        )

    raw_interp_terms: list[Mapping[str, Any]] = []
    reconstructed_interp_terms: list[Mapping[str, Any]] = []
    interp_items = require_array(upper_obj["interp_terms"], "$.upper.interp_terms")
    for index, item in enumerate(interp_items):
        path = f"$.upper.interp_terms[{index}]"
        term = require_object(item, path)
        check_keys(term, path, required=("weight", "i", "j"))
        raw_weight, reconstructed_weight = converter.decimal(
            term["weight"], f"{path}.weight"
        )
        i = point_json(term["i"], f"{path}.i", steps)
        j = point_json(term["j"], f"{path}.j", steps)
        raw_interp_terms.append({"weight": raw_weight, "i": i, "j": j})
        reconstructed_interp_terms.append(
            {"weight": reconstructed_weight, "i": i, "j": j}
        )

    raw_square_terms: list[Mapping[str, Any]] = []
    reconstructed_square_terms: list[Mapping[str, Any]] = []
    square_items = require_array(upper_obj["square_terms"], "$.upper.square_terms")
    for index, item in enumerate(square_items):
        path = f"$.upper.square_terms[{index}]"
        term = require_object(item, path)
        check_keys(term, path, required=("weight", "form"))
        raw_weight, reconstructed_weight = converter.decimal(
            term["weight"], f"{path}.weight"
        )
        form_path = f"{path}.form"
        form = require_object(term["form"], form_path)
        check_keys(form, form_path, required=("const", "grad"))
        raw_const, reconstructed_const = converter.decimal(
            form["const"], f"{form_path}.const"
        )
        raw_form_grad, reconstructed_form_grad = converter.vector(
            form["grad"], f"{form_path}.grad", steps + 1
        )
        raw_square_terms.append(
            {
                "weight": raw_weight,
                "form": {"const": raw_const, "grad": raw_form_grad},
            }
        )
        reconstructed_square_terms.append(
            {
                "weight": reconstructed_weight,
                "form": {
                    "const": reconstructed_const,
                    "grad": reconstructed_form_grad,
                },
            }
        )

    common = {
        "schema_version": exact.SCHEMA_VERSION,
        "steps": steps,
        "declared_point_count": point_count,
        "declared_constraint_count": constraint_count,
    }
    raw_exact: Mapping[str, Any] = {
        **common,
        "source": f"{source} | raw exact decimal interpretation",
        "expect": raw_expect,
        "primal": {"grad": raw_grad, "value": raw_value},
        "upper": {
            "bound": raw_bound,
            "objective": objective,
            "interp_terms": raw_interp_terms,
            "square_terms": raw_square_terms,
        },
    }
    reconstructed_exact: Mapping[str, Any] = {
        **common,
        "source": (
            f"{source} | reconstructed exact candidate via {policy.method}"
        ),
        "expect": reconstructed_expect,
        "primal": {
            "grad": reconstructed_grad,
            "value": reconstructed_value,
        },
        "upper": {
            "bound": reconstructed_bound,
            "objective": objective,
            "interp_terms": reconstructed_interp_terms,
            "square_terms": reconstructed_square_terms,
        },
    }

    # Reuse the existing exact-v1 parser as a second, independent shape/index
    # validation pass.  This also guarantees the exact schema itself is not
    # extended by the approximate pipeline.
    try:
        exact.parse_bundle(raw_exact)
        exact.parse_bundle(reconstructed_exact)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(f"generated exact bundle is invalid: {exc}") from exc

    return (
        raw_exact,
        reconstructed_exact,
        policy,
        tuple(converter.entries),
        raw_expect,
        reconstructed_expect,
    )


def build_report(
    *,
    source_sha256: str,
    raw_exact_sha256: str,
    reconstructed_exact_sha256: str,
    policy: ReconstructionPolicy,
    entries: Sequence[ReconstructionEntry],
) -> Mapping[str, Any]:
    changed_count = sum(entry.source_exact != entry.reconstructed for entry in entries)
    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "kind": "lean-pep-reconstruction-report-v1",
        "generator_version": GENERATOR_VERSION,
        "source_sha256": source_sha256,
        "raw_exact_sha256": raw_exact_sha256,
        "reconstructed_exact_sha256": reconstructed_exact_sha256,
        "policy": {
            "method": policy.method,
            "max_denominator": policy.max_denominator,
            "max_abs_error": policy.max_abs_error_source,
            "max_abs_error_exact": rational_json(policy.max_abs_error),
        },
        "entry_count": len(entries),
        "changed_entry_count": changed_count,
        "entries": [
            {
                "path": entry.path,
                "source": entry.source,
                "source_exact": rational_json(entry.source_exact),
                "reconstructed": rational_json(entry.reconstructed),
                "delta": rational_json(entry.delta),
                "absolute_error": rational_json(entry.absolute_error),
                "changed": entry.source_exact != entry.reconstructed,
            }
            for entry in entries
        ],
    }


def build_manifest(
    *,
    source_sha256: str,
    raw_exact_sha256: str,
    reconstructed_exact_sha256: str,
    reconstruction_report_sha256: str,
    raw_expect: str,
    reconstructed_expect: str,
) -> Mapping[str, Any]:
    return {
        "schema_version": MANIFEST_SCHEMA_VERSION,
        "kind": "lean-pep-approximate-audit-comparison-v1",
        "generator_version": GENERATOR_VERSION,
        "hashes": {
            "source_sha256": source_sha256,
            "raw_exact_sha256": raw_exact_sha256,
            "reconstructed_exact_sha256": reconstructed_exact_sha256,
            "reconstruction_report_sha256": reconstruction_report_sha256,
        },
        "tracks": {
            "raw": {
                "expected_audit": raw_expect,
                "meaning": (
                    "exact audit of the original finite base-10 strings; no repair or rounding"
                ),
            },
            "reconstructed": {
                "expected_audit": reconstructed_expect,
                "meaning": (
                    "exact audit of a nearby candidate produced by the recorded reconstruction policy"
                ),
            },
        },
        "interpretation": (
            "reconstructed acceptance does not imply that the raw numerical candidate was accepted"
        ),
    }


def render_expect_theorem(
    *,
    theorem_prefix: str,
    namespace: str,
    expect: str,
) -> list[str]:
    if expect == "accepted":
        return [
            f"theorem {theorem_prefix}BundleQ_check :",
            f"    {FD}.checkExactBundleQ {namespace}.bundleQ = true := by",
            f"  exact {namespace}.bundleQ_check",
            "",
        ]
    if expect == "rejected":
        return [
            f"theorem {theorem_prefix}BundleQ_rejected :",
            f"    {FD}.checkExactBundleQ {namespace}.bundleQ = false := by",
            f"  exact {namespace}.bundleQ_rejected",
            "",
        ]
    return []


def render_comparison_lean(
    *,
    steps: int,
    raw_namespace: str,
    reconstructed_namespace: str,
    comparison_namespace: str,
    source_sha256: str,
    raw_exact_sha256: str,
    reconstructed_exact_sha256: str,
    reconstruction_report_sha256: str,
    comparison_manifest_sha256: str,
    raw_expect: str,
    reconstructed_expect: str,
) -> str:
    raw_parts = exact.validate_namespace(raw_namespace)
    reconstructed_parts = exact.validate_namespace(reconstructed_namespace)
    comparison_parts = exact.validate_namespace(comparison_namespace)
    if raw_parts == reconstructed_parts or raw_parts == comparison_parts or reconstructed_parts == comparison_parts:
        raise ApproxFormatError("raw, reconstructed, and comparison namespaces must differ")

    lines: list[str] = [
        f"import {FD}.ApproximateAudit",
        f"import {raw_namespace}",
        f"import {reconstructed_namespace}",
        "",
        "/-!",
        "This file is generated by `tools/prepare_approx_bundle.py`.",
        "It compares two exact Lean audits with distinct semantics:",
        "the raw base-10 interpretation and the reconstructed candidate.",
        "-/",
        "",
    ]
    lines.extend(exact.render_namespace_open(comparison_parts))
    lines.extend(
        [
            "",
            f"def provenanceQ : {FD}.ApproxAuditProvenanceQ :=",
            f"  {{ sourceSha256 := {exact.lean_string(source_sha256)}",
            f"    rawExactSha256 := {exact.lean_string(raw_exact_sha256)}",
            "    reconstructedExactSha256 := "
            f"{exact.lean_string(reconstructed_exact_sha256)}",
            "    reconstructionReportSha256 := "
            f"{exact.lean_string(reconstruction_report_sha256)}",
            "    comparisonManifestSha256 := "
            f"{exact.lean_string(comparison_manifest_sha256)} }}",
            "",
            f"def comparisonQ : {FD}.ApproxAuditComparisonQ {steps} :=",
            f"  {FD}.auditApproximatePairQ provenanceQ",
            f"    {raw_namespace}.bundleQ",
            f"    {reconstructed_namespace}.bundleQ",
            "",
        ]
    )
    lines.extend(
        render_expect_theorem(
            theorem_prefix="raw",
            namespace=raw_namespace,
            expect=raw_expect,
        )
    )
    lines.extend(
        render_expect_theorem(
            theorem_prefix="reconstructed",
            namespace=reconstructed_namespace,
            expect=reconstructed_expect,
        )
    )
    lines.extend(exact.render_namespace_close(comparison_parts))
    lines.append("")
    return "\n".join(lines)


def prepare_artifacts(
    raw: Any,
    *,
    raw_namespace: str,
    reconstructed_namespace: str,
    comparison_namespace: str,
) -> PreparedArtifacts:
    (
        raw_exact,
        reconstructed_exact,
        policy,
        entries,
        raw_expect,
        reconstructed_expect,
    ) = build_exact_tracks(raw)
    source_obj = require_object(raw, "$")
    source_sha256 = canonical_sha256(source_obj)
    raw_exact_sha256 = canonical_sha256(raw_exact)
    reconstructed_exact_sha256 = canonical_sha256(reconstructed_exact)
    report = build_report(
        source_sha256=source_sha256,
        raw_exact_sha256=raw_exact_sha256,
        reconstructed_exact_sha256=reconstructed_exact_sha256,
        policy=policy,
        entries=entries,
    )
    reconstruction_report_sha256 = canonical_sha256(report)
    manifest = build_manifest(
        source_sha256=source_sha256,
        raw_exact_sha256=raw_exact_sha256,
        reconstructed_exact_sha256=reconstructed_exact_sha256,
        reconstruction_report_sha256=reconstruction_report_sha256,
        raw_expect=raw_expect,
        reconstructed_expect=reconstructed_expect,
    )
    comparison_manifest_sha256 = canonical_sha256(manifest)
    comparison_lean = render_comparison_lean(
        steps=require_int(source_obj["steps"], "$.steps", minimum=0),
        raw_namespace=raw_namespace,
        reconstructed_namespace=reconstructed_namespace,
        comparison_namespace=comparison_namespace,
        source_sha256=source_sha256,
        raw_exact_sha256=raw_exact_sha256,
        reconstructed_exact_sha256=reconstructed_exact_sha256,
        reconstruction_report_sha256=reconstruction_report_sha256,
        comparison_manifest_sha256=comparison_manifest_sha256,
        raw_expect=raw_expect,
        reconstructed_expect=reconstructed_expect,
    )
    return PreparedArtifacts(
        raw_exact=raw_exact,
        reconstructed_exact=reconstructed_exact,
        report=report,
        manifest=manifest,
        comparison_lean=comparison_lean,
    )


def load_json(path: Path) -> Mapping[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle, object_pairs_hook=exact.reject_duplicate_pairs)
    except OSError as exc:
        raise ApproxFormatError(f"cannot read {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ApproxFormatError(
            f"invalid JSON at line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def render_json(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value,
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
        separators=(",", ": "),
    ) + "\n"


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(content)
        os.replace(temp_name, path)
    except BaseException:
        try:
            os.unlink(temp_name)
        except OSError:
            pass
        raise


def rendered_outputs(artifacts: PreparedArtifacts) -> tuple[str, str, str, str, str]:
    return (
        render_json(artifacts.raw_exact),
        render_json(artifacts.reconstructed_exact),
        render_json(artifacts.report),
        render_json(artifacts.manifest),
        artifacts.comparison_lean,
    )


def write_or_check_outputs(
    paths: OutputPaths,
    rendered: Sequence[str],
    *,
    check: bool,
) -> None:
    output_paths = (
        paths.raw_exact,
        paths.reconstructed_exact,
        paths.report,
        paths.manifest,
        paths.comparison_lean,
    )
    for path, content in zip(output_paths, rendered, strict=True):
        if check:
            try:
                existing = path.read_text(encoding="utf-8")
            except OSError as exc:
                raise ApproxFormatError(f"cannot read generated output {path}: {exc}") from exc
            if existing != content:
                raise ApproxFormatError(
                    f"generated output is stale: {path}; regenerate it"
                )
        else:
            atomic_write(path, content)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Interpret approximate decimal strings exactly and prepare raw/reconstructed exact PEP bundles."
        )
    )
    parser.add_argument("input", type=Path, help="approximate-format-v1 JSON input")
    parser.add_argument("--raw-exact", required=True, type=Path)
    parser.add_argument("--reconstructed-exact", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--comparison-lean", required=True, type=Path)
    parser.add_argument("--raw-namespace", required=True)
    parser.add_argument("--reconstructed-namespace", required=True)
    parser.add_argument("--comparison-namespace", required=True)
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify all generated outputs without rewriting them",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        raw = load_json(args.input)
        artifacts = prepare_artifacts(
            raw,
            raw_namespace=args.raw_namespace,
            reconstructed_namespace=args.reconstructed_namespace,
            comparison_namespace=args.comparison_namespace,
        )
        paths = OutputPaths(
            raw_exact=args.raw_exact,
            reconstructed_exact=args.reconstructed_exact,
            report=args.report,
            manifest=args.manifest,
            comparison_lean=args.comparison_lean,
        )
        write_or_check_outputs(
            paths,
            rendered_outputs(artifacts),
            check=args.check,
        )
        return 0
    except (ApproxFormatError, exact.ImportFormatError) as exc:
        print(f"prepare_approx_bundle.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
