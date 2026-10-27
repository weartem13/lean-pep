#!/usr/bin/env python3
"""Prepare raw and reconstructed exact Gram-PEP bundles from decimal strings.

The approximate Gram boundary is deliberately separate from both exact JSON
schemas.  Every mathematical scalar is supplied as a finite base-10 string.
This script interprets those strings exactly, emits an unchanged
``external-gram-format-v1`` raw bundle, and emits a second exact bundle produced
by an explicit rational-reconstruction policy.

The script is an untrusted preprocessor.  Both generated bundles are passed
through ``import_exact_gram_bundle.py`` and are independently audited by Lean's
existing ``ExactGramBundleQ`` checker.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

import import_exact_bundle as base
import import_exact_gram_bundle as exact
import prepare_approx_bundle as common

GENERATOR_VERSION = "v0.11.1"
APPROX_SCHEMA_VERSION = 1
REPORT_SCHEMA_VERSION = 1
MANIFEST_SCHEMA_VERSION = 1
GP = "LeanPEP.GramPEP"

ApproxFormatError = common.ApproxFormatError
ApproxGramFormatError = ApproxFormatError
canonical_sha256 = common.canonical_sha256
ReconstructionPolicy = common.ReconstructionPolicy
ReconstructionEntry = common.ReconstructionEntry
CandidateConverter = common.CandidateConverter


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


def fail(path: str, message: str) -> NoReturn:
    raise ApproxFormatError(f"{path}: {message}")


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


def convert_vector(
    converter: CandidateConverter,
    value: Any,
    path: str,
    expected_length: int,
) -> tuple[list[dict[str, int]], list[dict[str, int]]]:
    return converter.vector(value, path, expected_length)


def convert_matrix(
    converter: CandidateConverter,
    value: Any,
    path: str,
    rows: int,
    cols: int,
) -> tuple[list[list[dict[str, int]]], list[list[dict[str, int]]]]:
    items = require_array(value, path)
    if len(items) != rows:
        fail(path, f"expected exactly {rows} rows, got {len(items)}")
    raw_rows: list[list[dict[str, int]]] = []
    reconstructed_rows: list[list[dict[str, int]]] = []
    for i, row in enumerate(items):
        raw_row, reconstructed_row = convert_vector(
            converter, row, f"{path}[{i}]", cols
        )
        raw_rows.append(raw_row)
        reconstructed_rows.append(reconstructed_row)
    return raw_rows, reconstructed_rows


def convert_linear_expr(
    converter: CandidateConverter,
    value: Any,
    path: str,
    p: int,
    m: int,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    obj = require_object(value, path)
    check_keys(obj, path, required=("const", "value_coeff", "gram_coeff"))
    raw_const, reconstructed_const = converter.decimal(
        obj["const"], f"{path}.const"
    )
    raw_value, reconstructed_value = convert_vector(
        converter, obj["value_coeff"], f"{path}.value_coeff", p
    )
    raw_gram, reconstructed_gram = convert_matrix(
        converter, obj["gram_coeff"], f"{path}.gram_coeff", m, m
    )
    return (
        {
            "const": raw_const,
            "value_coeff": raw_value,
            "gram_coeff": raw_gram,
        },
        {
            "const": reconstructed_const,
            "value_coeff": reconstructed_value,
            "gram_coeff": reconstructed_gram,
        },
    )


def convert_factor_cert(
    converter: CandidateConverter,
    value: Any,
    path: str,
    m: int,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    obj = require_object(value, path)
    check_keys(obj, path, required=("factors",))
    items = require_array(obj["factors"], f"{path}.factors")
    raw_factors: list[Mapping[str, Any]] = []
    reconstructed_factors: list[Mapping[str, Any]] = []
    for k, item in enumerate(items):
        item_path = f"{path}.factors[{k}]"
        fobj = require_object(item, item_path)
        check_keys(fobj, item_path, required=("weight", "vector"))
        raw_weight, reconstructed_weight = converter.decimal(
            fobj["weight"], f"{item_path}.weight"
        )
        raw_vector, reconstructed_vector = convert_vector(
            converter, fobj["vector"], f"{item_path}.vector", m
        )
        raw_factors.append({"weight": raw_weight, "vector": raw_vector})
        reconstructed_factors.append(
            {"weight": reconstructed_weight, "vector": reconstructed_vector}
        )
    return {"factors": raw_factors}, {"factors": reconstructed_factors}


def copy_declared(value: Any, path: str = "$.declared") -> Mapping[str, int]:
    obj = require_object(value, path)
    fields = (
        "point_count",
        "gram_basis_count",
        "ordered_pair_count",
        "assumption_count",
        "primal_factor_count",
        "upper_interp_term_count",
        "upper_assumption_term_count",
        "dual_factor_count",
    )
    check_keys(obj, path, required=fields)
    return {
        field: require_int(obj[field], f"{path}.{field}", minimum=0)
        for field in fields
    }


def copy_ordering(
    value: Any, path: str = "$.ordering"
) -> tuple[Mapping[str, Any], int, int]:
    obj = require_object(value, path)
    check_keys(obj, path, required=("points", "gram_basis"))
    try:
        points = exact.parse_labels(obj["points"], f"{path}.points")
        gram_basis = exact.parse_labels(
            obj["gram_basis"], f"{path}.gram_basis"
        )
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc
    return (
        {"points": list(points), "gram_basis": list(gram_basis)},
        len(points),
        len(gram_basis),
    )


def convert_model(
    converter: CandidateConverter,
    value: Any,
    path: str,
    p: int,
    m: int,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    obj = require_object(value, path)
    check_keys(obj, path, required=("position", "gradient", "assumptions"))
    raw_position, reconstructed_position = convert_matrix(
        converter, obj["position"], f"{path}.position", p, m
    )
    raw_gradient, reconstructed_gradient = convert_matrix(
        converter, obj["gradient"], f"{path}.gradient", p, m
    )

    assumption_items = require_array(obj["assumptions"], f"{path}.assumptions")
    raw_assumptions: list[Mapping[str, Any]] = []
    reconstructed_assumptions: list[Mapping[str, Any]] = []
    names: set[str] = set()
    for k, item in enumerate(assumption_items):
        item_path = f"{path}.assumptions[{k}]"
        aobj = require_object(item, item_path)
        check_keys(aobj, item_path, required=("name", "expr"))
        name = require_string(aobj["name"], f"{item_path}.name")
        if not name:
            fail(f"{item_path}.name", "must not be empty")
        if name in names:
            fail(f"{item_path}.name", f"duplicate assumption name {name!r}")
        names.add(name)
        raw_expr, reconstructed_expr = convert_linear_expr(
            converter, aobj["expr"], f"{item_path}.expr", p, m
        )
        raw_assumptions.append({"name": name, "expr": raw_expr})
        reconstructed_assumptions.append(
            {"name": name, "expr": reconstructed_expr}
        )

    return (
        {
            "position": raw_position,
            "gradient": raw_gradient,
            "assumptions": raw_assumptions,
        },
        {
            "position": reconstructed_position,
            "gradient": reconstructed_gradient,
            "assumptions": reconstructed_assumptions,
        },
    )


def convert_primal(
    converter: CandidateConverter,
    value: Any,
    path: str,
    p: int,
    m: int,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    obj = require_object(value, path)
    check_keys(obj, path, required=("gram", "value", "gram_factor"))
    raw_gram, reconstructed_gram = convert_matrix(
        converter, obj["gram"], f"{path}.gram", m, m
    )
    raw_value, reconstructed_value = convert_vector(
        converter, obj["value"], f"{path}.value", p
    )
    raw_factor, reconstructed_factor = convert_factor_cert(
        converter, obj["gram_factor"], f"{path}.gram_factor", m
    )
    return (
        {
            "gram": raw_gram,
            "value": raw_value,
            "gram_factor": raw_factor,
        },
        {
            "gram": reconstructed_gram,
            "value": reconstructed_value,
            "gram_factor": reconstructed_factor,
        },
    )


def convert_upper(
    converter: CandidateConverter,
    value: Any,
    path: str,
    p: int,
    m: int,
    assumption_count: int,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    obj = require_object(value, path)
    check_keys(
        obj,
        path,
        required=(
            "bound",
            "objective",
            "interp_terms",
            "assumption_terms",
            "dual_matrix",
            "dual_factor",
        ),
    )
    raw_bound, reconstructed_bound = converter.decimal(
        obj["bound"], f"{path}.bound"
    )
    raw_objective, reconstructed_objective = convert_linear_expr(
        converter, obj["objective"], f"{path}.objective", p, m
    )

    raw_interp_terms: list[Mapping[str, Any]] = []
    reconstructed_interp_terms: list[Mapping[str, Any]] = []
    interp_items = require_array(obj["interp_terms"], f"{path}.interp_terms")
    for k, item in enumerate(interp_items):
        item_path = f"{path}.interp_terms[{k}]"
        iobj = require_object(item, item_path)
        check_keys(iobj, item_path, required=("weight", "i", "j"))
        i = require_int(iobj["i"], f"{item_path}.i", minimum=0)
        j = require_int(iobj["j"], f"{item_path}.j", minimum=0)
        if i >= p:
            fail(f"{item_path}.i", f"index {i} is outside 0..{p - 1}")
        if j >= p:
            fail(f"{item_path}.j", f"index {j} is outside 0..{p - 1}")
        raw_weight, reconstructed_weight = converter.decimal(
            iobj["weight"], f"{item_path}.weight"
        )
        raw_interp_terms.append({"weight": raw_weight, "i": i, "j": j})
        reconstructed_interp_terms.append(
            {"weight": reconstructed_weight, "i": i, "j": j}
        )

    raw_assumption_terms: list[Mapping[str, Any]] = []
    reconstructed_assumption_terms: list[Mapping[str, Any]] = []
    assumption_items = require_array(
        obj["assumption_terms"], f"{path}.assumption_terms"
    )
    for k, item in enumerate(assumption_items):
        item_path = f"{path}.assumption_terms[{k}]"
        aobj = require_object(item, item_path)
        check_keys(aobj, item_path, required=("weight", "index"))
        index = require_int(aobj["index"], f"{item_path}.index", minimum=0)
        if index >= assumption_count:
            fail(
                f"{item_path}.index",
                f"index {index} is outside 0..{assumption_count - 1}",
            )
        raw_weight, reconstructed_weight = converter.decimal(
            aobj["weight"], f"{item_path}.weight"
        )
        raw_assumption_terms.append({"weight": raw_weight, "index": index})
        reconstructed_assumption_terms.append(
            {"weight": reconstructed_weight, "index": index}
        )

    raw_dual, reconstructed_dual = convert_matrix(
        converter, obj["dual_matrix"], f"{path}.dual_matrix", m, m
    )
    raw_dual_factor, reconstructed_dual_factor = convert_factor_cert(
        converter, obj["dual_factor"], f"{path}.dual_factor", m
    )
    return (
        {
            "bound": raw_bound,
            "objective": raw_objective,
            "interp_terms": raw_interp_terms,
            "assumption_terms": raw_assumption_terms,
            "dual_matrix": raw_dual,
            "dual_factor": raw_dual_factor,
        },
        {
            "bound": reconstructed_bound,
            "objective": reconstructed_objective,
            "interp_terms": reconstructed_interp_terms,
            "assumption_terms": reconstructed_assumption_terms,
            "dual_matrix": reconstructed_dual,
            "dual_factor": reconstructed_dual_factor,
        },
    )


def build_exact_tracks(
    raw: Any,
) -> tuple[
    Mapping[str, Any],
    Mapping[str, Any],
    ReconstructionPolicy,
    tuple[ReconstructionEntry, ...],
    str,
    str,
    int,
    int,
]:
    obj = require_object(raw, "$")
    check_keys(
        obj,
        "$",
        required=(
            "schema_version",
            "source",
            "declared",
            "ordering",
            "policy",
            "model",
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

    declared = copy_declared(obj["declared"])
    ordering, p, m = copy_ordering(obj["ordering"])
    policy = common.parse_policy(obj["policy"])
    raw_expect, reconstructed_expect = common.parse_expect(obj.get("expect"))
    converter = CandidateConverter(policy)

    raw_model, reconstructed_model = convert_model(
        converter, obj["model"], "$.model", p, m
    )
    assumption_count = len(raw_model["assumptions"])
    raw_primal, reconstructed_primal = convert_primal(
        converter, obj["primal"], "$.primal", p, m
    )
    raw_upper, reconstructed_upper = convert_upper(
        converter,
        obj["upper"],
        "$.upper",
        p,
        m,
        assumption_count,
    )

    common_fields = {
        "schema_version": exact.SCHEMA_VERSION,
        "declared": declared,
        "ordering": ordering,
    }
    raw_exact: Mapping[str, Any] = {
        **common_fields,
        "source": f"{source} | raw exact decimal interpretation",
        "model": raw_model,
        "primal": raw_primal,
        "upper": raw_upper,
        "expect": raw_expect,
    }
    reconstructed_exact: Mapping[str, Any] = {
        **common_fields,
        "source": f"{source} | reconstructed exact candidate via {policy.method}",
        "model": reconstructed_model,
        "primal": reconstructed_primal,
        "upper": reconstructed_upper,
        "expect": reconstructed_expect,
    }

    try:
        exact.parse_bundle(raw_exact)
        exact.parse_bundle(reconstructed_exact)
    except exact.ImportFormatError as exc:
        raise ApproxFormatError(
            f"generated exact Gram bundle is invalid: {exc}"
        ) from exc

    return (
        raw_exact,
        reconstructed_exact,
        policy,
        tuple(converter.entries),
        raw_expect,
        reconstructed_expect,
        p,
        m,
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
        "kind": "lean-pep-gram-reconstruction-report-v1",
        "generator_version": GENERATOR_VERSION,
        "source_sha256": source_sha256,
        "raw_exact_sha256": raw_exact_sha256,
        "reconstructed_exact_sha256": reconstructed_exact_sha256,
        "policy": {
            "method": policy.method,
            "max_denominator": policy.max_denominator,
            "max_abs_error": policy.max_abs_error_source,
            "max_abs_error_exact": common.rational_json(policy.max_abs_error),
        },
        "entry_count": len(entries),
        "changed_entry_count": changed_count,
        "entries": [
            {
                "path": entry.path,
                "source": entry.source,
                "source_exact": common.rational_json(entry.source_exact),
                "reconstructed": common.rational_json(entry.reconstructed),
                "delta": common.rational_json(entry.delta),
                "absolute_error": common.rational_json(entry.absolute_error),
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
    p: int,
    m: int,
) -> Mapping[str, Any]:
    return {
        "schema_version": MANIFEST_SCHEMA_VERSION,
        "kind": "lean-pep-approximate-gram-audit-comparison-v1",
        "generator_version": GENERATOR_VERSION,
        "dimensions": {"point_count": p, "gram_basis_count": m},
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
                    "exact Gram audit of the original finite base-10 strings; no repair or rounding"
                ),
            },
            "reconstructed": {
                "expected_audit": reconstructed_expect,
                "meaning": (
                    "exact Gram audit of a nearby candidate produced by the recorded reconstruction policy"
                ),
            },
        },
        "interpretation": (
            "reconstructed Gram acceptance does not imply that the raw numerical Gram artifact was accepted"
        ),
    }


def render_expect_theorem(
    *, theorem_prefix: str, namespace: str, expect: str
) -> list[str]:
    if expect == "accepted":
        return [
            f"theorem {theorem_prefix}BundleQ_check :",
            f"    {GP}.checkExactGramBundleQ {namespace}.bundleQ = true := by",
            f"  exact {namespace}.bundleQ_check",
            "",
        ]
    if expect == "rejected":
        return [
            f"theorem {theorem_prefix}BundleQ_rejected :",
            f"    {GP}.checkExactGramBundleQ {namespace}.bundleQ = false := by",
            f"  exact {namespace}.bundleQ_rejected",
            "",
        ]
    return []


def render_comparison_lean(
    *,
    p: int,
    m: int,
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
    if (
        raw_parts == reconstructed_parts
        or raw_parts == comparison_parts
        or reconstructed_parts == comparison_parts
    ):
        raise ApproxFormatError(
            "raw, reconstructed, and comparison namespaces must differ"
        )

    lines: list[str] = [
        f"import {GP}.ApproximateAudit",
        f"import {raw_namespace}",
        f"import {reconstructed_namespace}",
        "",
        "/-!",
        "This file is generated by `tools/prepare_approx_gram_bundle.py`.",
        "It compares two exact Gram-bundle audits with distinct semantics:",
        "the raw base-10 interpretation and the reconstructed candidate.",
        "-/",
        "",
    ]
    lines.extend(exact.render_namespace_open(comparison_parts))
    lines.extend(
        [
            "",
            f"def provenanceQ : {GP}.ApproxGramAuditProvenanceQ :=",
            f"  {{ sourceSha256 := {exact.lean_string(source_sha256)}",
            f"    rawExactSha256 := {exact.lean_string(raw_exact_sha256)}",
            "    reconstructedExactSha256 := "
            f"{exact.lean_string(reconstructed_exact_sha256)}",
            "    reconstructionReportSha256 := "
            f"{exact.lean_string(reconstruction_report_sha256)}",
            "    comparisonManifestSha256 := "
            f"{exact.lean_string(comparison_manifest_sha256)} }}",
            "",
            f"def comparisonQ : {GP}.ApproxGramAuditComparisonQ {p} {m} :=",
            f"  {GP}.auditApproximateGramPairQ provenanceQ",
            f"    {raw_namespace}.bundleQ",
            f"    {reconstructed_namespace}.bundleQ",
            "",
        ]
    )
    lines.extend(
        render_expect_theorem(
            theorem_prefix="raw", namespace=raw_namespace, expect=raw_expect
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
        p,
        m,
    ) = build_exact_tracks(raw)
    source_obj = require_object(raw, "$")
    source_sha256 = common.canonical_sha256(source_obj)
    raw_exact_sha256 = common.canonical_sha256(raw_exact)
    reconstructed_exact_sha256 = common.canonical_sha256(reconstructed_exact)
    report = build_report(
        source_sha256=source_sha256,
        raw_exact_sha256=raw_exact_sha256,
        reconstructed_exact_sha256=reconstructed_exact_sha256,
        policy=policy,
        entries=entries,
    )
    reconstruction_report_sha256 = common.canonical_sha256(report)
    manifest = build_manifest(
        source_sha256=source_sha256,
        raw_exact_sha256=raw_exact_sha256,
        reconstructed_exact_sha256=reconstructed_exact_sha256,
        reconstruction_report_sha256=reconstruction_report_sha256,
        raw_expect=raw_expect,
        reconstructed_expect=reconstructed_expect,
        p=p,
        m=m,
    )
    comparison_manifest_sha256 = common.canonical_sha256(manifest)
    comparison_lean = render_comparison_lean(
        p=p,
        m=m,
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
            return json.load(handle, object_pairs_hook=base.reject_duplicate_pairs)
    except OSError as exc:
        raise ApproxFormatError(f"cannot read {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ApproxFormatError(
            f"invalid JSON at line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc
    except base.ImportFormatError as exc:
        raise ApproxFormatError(str(exc)) from exc


def render_json(value: Mapping[str, Any]) -> str:
    return common.render_json(value)


def rendered_outputs(
    artifacts: PreparedArtifacts,
) -> tuple[str, str, str, str, str]:
    return (
        render_json(artifacts.raw_exact),
        render_json(artifacts.reconstructed_exact),
        render_json(artifacts.report),
        render_json(artifacts.manifest),
        artifacts.comparison_lean,
    )


def write_or_check_outputs(
    paths: OutputPaths, rendered: Sequence[str], *, check: bool
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
                raise ApproxFormatError(
                    f"cannot read generated output {path}: {exc}"
                ) from exc
            if existing != content:
                raise ApproxFormatError(
                    f"generated output is stale: {path}; regenerate it"
                )
        else:
            common.atomic_write(path, content)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Interpret approximate Gram-bundle decimal strings exactly and prepare raw/reconstructed exact bundles."
        )
    )
    parser.add_argument(
        "input", type=Path, help="approximate-gram-format-v1 JSON input"
    )
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
            paths, rendered_outputs(artifacts), check=args.check
        )
        return 0
    except (ApproxFormatError, exact.ImportFormatError, base.ImportFormatError) as exc:
        print(f"prepare_approx_gram_bundle.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
