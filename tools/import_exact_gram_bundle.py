#!/usr/bin/env python3
"""Generate a Lean module from a strict exact Gram-PEP JSON bundle.

The importer is deliberately untrusted. It validates source shape, dimensions,
indices, labels, and exact rational syntax, then emits ordinary Lean data. The
Lean-side `ExactGramBundleQ` checker independently rechecks every mathematical
obligation.
"""

from __future__ import annotations

import argparse
import copy
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

import import_exact_bundle as base

GENERATOR_VERSION = "v0.11.0"
SCHEMA_VERSION = 1
GP = "LeanPEP.GramPEP"

ImportFormatError = base.ImportFormatError
reject_duplicate_pairs = base.reject_duplicate_pairs
load_json = base.load_json
atomic_write = base.atomic_write
validate_namespace = base.validate_namespace
lean_string = base.lean_string
lean_rat = base.lean_rat
indent_lines = base.indent_lines
render_namespace_open = base.render_namespace_open
render_namespace_close = base.render_namespace_close
canonical_json_sha256 = base.canonical_json_sha256


def fail(path: str, message: str) -> NoReturn:
    raise ImportFormatError(f"{path}: {message}")


def require_object(value: Any, path: str) -> Mapping[str, Any]:
    return base.require_object(value, path)


def require_array(value: Any, path: str) -> Sequence[Any]:
    return base.require_array(value, path)


def require_string(value: Any, path: str) -> str:
    return base.require_string(value, path)


def require_int(value: Any, path: str, *, minimum: int | None = None) -> int:
    return base.require_int(value, path, minimum=minimum)


def check_keys(
    obj: Mapping[str, Any],
    path: str,
    *,
    required: Sequence[str],
    optional: Sequence[str] = (),
) -> None:
    base.check_keys(obj, path, required=required, optional=optional)


def parse_rational(value: Any, path: str) -> Fraction:
    return base.parse_rational(value, path)


@dataclass(frozen=True)
class LinearExprSpec:
    const: Fraction
    value_coeff: tuple[Fraction, ...]
    gram_coeff: tuple[tuple[Fraction, ...], ...]


@dataclass(frozen=True)
class NamedAssumptionSpec:
    name: str
    expr: LinearExprSpec


@dataclass(frozen=True)
class RankOneFactorSpec:
    weight: Fraction
    vector: tuple[Fraction, ...]


@dataclass(frozen=True)
class FactorCertSpec:
    factors: tuple[RankOneFactorSpec, ...]


@dataclass(frozen=True)
class DeclaredSpec:
    point_count: int
    gram_basis_count: int
    ordered_pair_count: int
    assumption_count: int
    primal_factor_count: int
    upper_interp_term_count: int
    upper_assumption_term_count: int
    dual_factor_count: int


@dataclass(frozen=True)
class OrderingSpec:
    points: tuple[str, ...]
    gram_basis: tuple[str, ...]


@dataclass(frozen=True)
class ModelSpec:
    position: tuple[tuple[Fraction, ...], ...]
    gradient: tuple[tuple[Fraction, ...], ...]
    assumptions: tuple[NamedAssumptionSpec, ...]


@dataclass(frozen=True)
class PrimalSpec:
    gram: tuple[tuple[Fraction, ...], ...]
    value: tuple[Fraction, ...]
    gram_factor: FactorCertSpec


@dataclass(frozen=True)
class InterpTermSpec:
    weight: Fraction
    i: int
    j: int


@dataclass(frozen=True)
class AssumptionTermSpec:
    weight: Fraction
    index: int


@dataclass(frozen=True)
class UpperSpec:
    bound: Fraction
    objective: LinearExprSpec
    interp_terms: tuple[InterpTermSpec, ...]
    assumption_terms: tuple[AssumptionTermSpec, ...]
    dual_matrix: tuple[tuple[Fraction, ...], ...]
    dual_factor: FactorCertSpec


@dataclass(frozen=True)
class BundleSpec:
    source: str
    declared: DeclaredSpec
    ordering: OrderingSpec
    model: ModelSpec
    primal: PrimalSpec
    upper: UpperSpec
    expect: str
    source_sha256: str

    @property
    def point_count(self) -> int:
        return len(self.ordering.points)

    @property
    def gram_basis_count(self) -> int:
        return len(self.ordering.gram_basis)


def parse_labels(value: Any, path: str) -> tuple[str, ...]:
    items = require_array(value, path)
    labels: list[str] = []
    for k, item in enumerate(items):
        label = require_string(item, f"{path}[{k}]")
        if not label:
            fail(f"{path}[{k}]", "label must not be empty")
        labels.append(label)
    if not labels:
        fail(path, "expected at least one label")
    if len(set(labels)) != len(labels):
        fail(path, "labels must be unique and preserve one unambiguous ordering")
    return tuple(labels)


def parse_rational_vector(
    value: Any, path: str, expected_length: int
) -> tuple[Fraction, ...]:
    items = require_array(value, path)
    if len(items) != expected_length:
        fail(path, f"expected exactly {expected_length} entries, got {len(items)}")
    return tuple(parse_rational(item, f"{path}[{k}]") for k, item in enumerate(items))


def parse_rational_matrix(
    value: Any, path: str, rows: int, cols: int
) -> tuple[tuple[Fraction, ...], ...]:
    items = require_array(value, path)
    if len(items) != rows:
        fail(path, f"expected exactly {rows} rows, got {len(items)}")
    return tuple(
        parse_rational_vector(row, f"{path}[{i}]", cols)
        for i, row in enumerate(items)
    )


def parse_linear_expr(value: Any, path: str, p: int, m: int) -> LinearExprSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("const", "value_coeff", "gram_coeff"))
    return LinearExprSpec(
        const=parse_rational(obj["const"], f"{path}.const"),
        value_coeff=parse_rational_vector(
            obj["value_coeff"], f"{path}.value_coeff", p
        ),
        gram_coeff=parse_rational_matrix(
            obj["gram_coeff"], f"{path}.gram_coeff", m, m
        ),
    )


def parse_factor(value: Any, path: str, m: int) -> RankOneFactorSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("weight", "vector"))
    return RankOneFactorSpec(
        weight=parse_rational(obj["weight"], f"{path}.weight"),
        vector=parse_rational_vector(obj["vector"], f"{path}.vector", m),
    )


def parse_factor_cert(value: Any, path: str, m: int) -> FactorCertSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("factors",))
    items = require_array(obj["factors"], f"{path}.factors")
    return FactorCertSpec(
        factors=tuple(
            parse_factor(item, f"{path}.factors[{k}]", m)
            for k, item in enumerate(items)
        )
    )


def parse_declared(value: Any, path: str) -> DeclaredSpec:
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
    values = {
        field: require_int(obj[field], f"{path}.{field}", minimum=0)
        for field in fields
    }
    return DeclaredSpec(**values)


def parse_model(value: Any, path: str, p: int, m: int) -> ModelSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("position", "gradient", "assumptions"))
    assumption_items = require_array(obj["assumptions"], f"{path}.assumptions")
    assumptions: list[NamedAssumptionSpec] = []
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
        assumptions.append(
            NamedAssumptionSpec(
                name=name,
                expr=parse_linear_expr(aobj["expr"], f"{item_path}.expr", p, m),
            )
        )
    return ModelSpec(
        position=parse_rational_matrix(obj["position"], f"{path}.position", p, m),
        gradient=parse_rational_matrix(obj["gradient"], f"{path}.gradient", p, m),
        assumptions=tuple(assumptions),
    )


def parse_primal(value: Any, path: str, p: int, m: int) -> PrimalSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("gram", "value", "gram_factor"))
    return PrimalSpec(
        gram=parse_rational_matrix(obj["gram"], f"{path}.gram", m, m),
        value=parse_rational_vector(obj["value"], f"{path}.value", p),
        gram_factor=parse_factor_cert(obj["gram_factor"], f"{path}.gram_factor", m),
    )


def parse_upper(value: Any, path: str, p: int, m: int, assumptions: int) -> UpperSpec:
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
    interp_items = require_array(obj["interp_terms"], f"{path}.interp_terms")
    interp_terms: list[InterpTermSpec] = []
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
        interp_terms.append(
            InterpTermSpec(
                weight=parse_rational(iobj["weight"], f"{item_path}.weight"),
                i=i,
                j=j,
            )
        )

    assumption_items = require_array(
        obj["assumption_terms"], f"{path}.assumption_terms"
    )
    assumption_terms: list[AssumptionTermSpec] = []
    for k, item in enumerate(assumption_items):
        item_path = f"{path}.assumption_terms[{k}]"
        aobj = require_object(item, item_path)
        check_keys(aobj, item_path, required=("weight", "index"))
        index = require_int(aobj["index"], f"{item_path}.index", minimum=0)
        if index >= assumptions:
            upper = assumptions - 1
            fail(
                f"{item_path}.index",
                f"index {index} is outside 0..{upper}",
            )
        assumption_terms.append(
            AssumptionTermSpec(
                weight=parse_rational(aobj["weight"], f"{item_path}.weight"),
                index=index,
            )
        )

    return UpperSpec(
        bound=parse_rational(obj["bound"], f"{path}.bound"),
        objective=parse_linear_expr(obj["objective"], f"{path}.objective", p, m),
        interp_terms=tuple(interp_terms),
        assumption_terms=tuple(assumption_terms),
        dual_matrix=parse_rational_matrix(
            obj["dual_matrix"], f"{path}.dual_matrix", m, m
        ),
        dual_factor=parse_factor_cert(obj["dual_factor"], f"{path}.dual_factor", m),
    )


def parse_bundle(raw: Any) -> BundleSpec:
    obj = require_object(raw, "$")
    check_keys(
        obj,
        "$",
        required=(
            "schema_version",
            "source",
            "declared",
            "ordering",
            "model",
            "primal",
            "upper",
        ),
        optional=("expect",),
    )
    schema = require_int(obj["schema_version"], "$.schema_version")
    if schema != SCHEMA_VERSION:
        fail(
            "$.schema_version",
            f"unsupported schema version {schema}; expected {SCHEMA_VERSION}",
        )
    source = require_string(obj["source"], "$.source")
    if not source:
        fail("$.source", "must not be empty")

    ordering_obj = require_object(obj["ordering"], "$.ordering")
    check_keys(ordering_obj, "$.ordering", required=("points", "gram_basis"))
    ordering = OrderingSpec(
        points=parse_labels(ordering_obj["points"], "$.ordering.points"),
        gram_basis=parse_labels(
            ordering_obj["gram_basis"], "$.ordering.gram_basis"
        ),
    )
    p = len(ordering.points)
    m = len(ordering.gram_basis)

    model = parse_model(obj["model"], "$.model", p, m)
    primal = parse_primal(obj["primal"], "$.primal", p, m)
    upper = parse_upper(obj["upper"], "$.upper", p, m, len(model.assumptions))
    expect = require_string(obj.get("expect", "unchecked"), "$.expect")
    if expect not in {"accepted", "rejected", "unchecked"}:
        fail("$.expect", "expected 'accepted', 'rejected', or 'unchecked'")

    return BundleSpec(
        source=source,
        declared=parse_declared(obj["declared"], "$.declared"),
        ordering=ordering,
        model=model,
        primal=primal,
        upper=upper,
        expect=expect,
        source_sha256=canonical_json_sha256(obj),
    )


def lean_vector(values: Sequence[Fraction]) -> str:
    return "![" + ", ".join(lean_rat(value) for value in values) + "]"


def lean_matrix(rows: Sequence[Sequence[Fraction]]) -> str:
    return "![" + ", ".join(lean_vector(row) for row in rows) + "]"


def lean_string_list(values: Sequence[str]) -> str:
    return "[" + ", ".join(lean_string(value) for value in values) + "]"


def render_linear_expr(expr: LinearExprSpec) -> list[str]:
    return [
        "{ constCoeff := " + lean_rat(expr.const),
        "  valueCoeff := " + lean_vector(expr.value_coeff),
        "  gramCoeff := " + lean_matrix(expr.gram_coeff) + " }",
    ]


def render_factor(factor: RankOneFactorSpec) -> list[str]:
    return [
        "{ weight := " + lean_rat(factor.weight),
        "  vector := " + lean_vector(factor.vector) + " }",
    ]


def render_record_list(items: Sequence[Any], renderer: Any) -> list[str]:
    if not items:
        return ["[]"]
    lines: list[str] = ["["]
    for k, item in enumerate(items):
        rendered = renderer(item)
        if k + 1 < len(items):
            rendered[-1] += ","
        lines.extend(indent_lines(rendered, 2))
    lines.append("]")
    return lines


def render_interp_term(term: InterpTermSpec) -> list[str]:
    return [
        "{ weight := " + lean_rat(term.weight),
        f"  i := {term.i}",
        f"  j := {term.j} }}",
    ]


def render_assumption_term(term: AssumptionTermSpec) -> list[str]:
    return [
        "{ weight := " + lean_rat(term.weight),
        f"  index := assumptionIndex{term.index}Q }}",
    ]


def render_module(spec: BundleSpec, namespace: str) -> str:
    ns_parts = validate_namespace(namespace)
    p = spec.point_count
    m = spec.gram_basis_count
    assumption_exprs = tuple(item.expr for item in spec.model.assumptions)
    assumption_names = tuple(item.name for item in spec.model.assumptions)
    used_assumption_indices = sorted({term.index for term in spec.upper.assumption_terms})

    lines: list[str] = [
        f"import {GP}.ExternalBundle",
        "",
        "/-!",
        "This file is generated by `tools/import_exact_gram_bundle.py`.",
        "Do not edit it by hand; regenerate it from the exact Gram JSON source.",
        "",
        f"Canonical JSON SHA-256: {spec.source_sha256}",
        f"Generator version: {GENERATOR_VERSION}",
        "-/",
        "",
    ]
    lines.extend(render_namespace_open(ns_parts))
    lines.append("")
    lines.extend(
        [
            f"def metadataQ : {GP}.ImportMetadataQ {p} {m} :=",
            f"  {{ schemaVersion := {SCHEMA_VERSION}",
            f"    declaredPointCount := {spec.declared.point_count}",
            f"    declaredGramBasisCount := {spec.declared.gram_basis_count}",
            f"    declaredOrderedPairCount := {spec.declared.ordered_pair_count}",
            f"    declaredAssumptionCount := {spec.declared.assumption_count}",
            f"    declaredPrimalFactorCount := {spec.declared.primal_factor_count}",
            f"    declaredUpperInterpTermCount := {spec.declared.upper_interp_term_count}",
            f"    declaredUpperAssumptionTermCount := {spec.declared.upper_assumption_term_count}",
            f"    declaredDualFactorCount := {spec.declared.dual_factor_count}",
            f"    pointOrder := {lean_string_list(spec.ordering.points)}",
            f"    gramBasisOrder := {lean_string_list(spec.ordering.gram_basis)}",
            f"    assumptionOrder := {lean_string_list(assumption_names)}",
            f"    sourceName := {lean_string(spec.source)}",
            f"    sourceSha256 := {lean_string(spec.source_sha256)}",
            f"    generatorVersion := {lean_string(GENERATOR_VERSION)} }}",
            "",
            f"def modelQ : {GP}.ModelQ {p} {m} :=",
            f"  {{ position := {lean_matrix(spec.model.position)}",
            f"    gradient := {lean_matrix(spec.model.gradient)}",
            "    assumptions :=",
        ]
    )
    lines.extend(indent_lines(render_record_list(assumption_exprs, render_linear_expr), 6))
    lines.append("  }")
    lines.append("")

    lines.extend(
        [
            f"def primalFactorQ : {GP}.PSDFactorCertQ {m} :=",
            "  { factors :=",
        ]
    )
    lines.extend(
        indent_lines(render_record_list(spec.primal.gram_factor.factors, render_factor), 6)
    )
    lines.append("  }")
    lines.extend(
        [
            "",
            f"def primalQ : {GP}.DataQ (Fin {p}) {m} :=",
            f"  {{ gram := {lean_matrix(spec.primal.gram)}",
            "    position := modelQ.position",
            "    gradient := modelQ.gradient",
            f"    value := {lean_vector(spec.primal.value)} }}",
            "",
        ]
    )

    for index in used_assumption_indices:
        lines.extend(
            [
                f"def assumptionIndex{index}Q : Fin modelQ.assumptions.length :=",
                f"  ⟨{index}, by simp [modelQ]⟩",
                "",
            ]
        )

    lines.extend(
        [
            f"def upperCertQ : {GP}.UpperCertQ modelQ :=",
            f"  {{ bound := {lean_rat(spec.upper.bound)}",
            "    objective :=",
        ]
    )
    lines.extend(indent_lines(render_linear_expr(spec.upper.objective), 6))
    lines.append("    interpTerms :=")
    lines.extend(
        indent_lines(render_record_list(spec.upper.interp_terms, render_interp_term), 6)
    )
    lines.append("    assumptionTerms :=")
    lines.extend(
        indent_lines(
            render_record_list(spec.upper.assumption_terms, render_assumption_term), 6
        )
    )
    lines.extend(
        [
            f"    dualMatrix := {lean_matrix(spec.upper.dual_matrix)}",
            "    dualFactor :=",
            "      { factors :=",
        ]
    )
    lines.extend(
        indent_lines(render_record_list(spec.upper.dual_factor.factors, render_factor), 10)
    )
    lines.extend(["      }", "  }", ""])

    lines.extend(
        [
            f"def bundleQ : {GP}.ExactGramBundleQ {p} {m} :=",
            "  { metadata := metadataQ",
            "    model := modelQ",
            "    primal := primalQ",
            "    primalFactor := primalFactorQ",
            "    upper := upperCertQ }",
            "",
            f"def auditQ : {GP}.ExactGramBundleAuditReportQ {p} {m} :=",
            f"  {GP}.auditExactGramBundleQ bundleQ",
            "",
        ]
    )

    if spec.expect == "accepted":
        lines.extend(
            [
                "theorem bundleQ_check :",
                f"    {GP}.checkExactGramBundleQ bundleQ = true := by",
                "  native_decide",
                "",
                "theorem bundleQ_sound_real :",
                f"    {GP}.checkImportMetadataQ bundleQ = true ∧",
                f"      {GP}.RealizesModelQ modelQ ({GP}.castDataQ primalQ) ∧",
                f"      {GP}.CoreFeasible ({GP}.castDataQ primalQ) ∧",
                f"      {GP}.AssumptionsFeasibleR modelQ ({GP}.castDataQ primalQ) ∧",
                f"      upperCertQ.objective.evalR ({GP}.castDataQ primalQ) =",
                "        (upperCertQ.bound : ℝ) ∧",
                f"      ∀ d : {GP}.DataR (Fin {p}) {m},",
                f"        {GP}.RealizesModelQ modelQ d →",
                f"        {GP}.CoreFeasible d →",
                f"        {GP}.AssumptionsFeasibleR modelQ d →",
                "        upperCertQ.objective.evalR d ≤ (upperCertQ.bound : ℝ) := by",
                "  simpa [bundleQ] using",
                f"    {GP}.checkExactGramBundleQ_sound_real bundleQ bundleQ_check",
                "",
            ]
        )
    elif spec.expect == "rejected":
        lines.extend(
            [
                "theorem bundleQ_rejected :",
                f"    {GP}.checkExactGramBundleQ bundleQ = false := by",
                "  native_decide",
                "",
            ]
        )

    lines.extend(render_namespace_close(ns_parts))
    lines.append("")
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate an exact Lean Gram-PEP bundle module from strict JSON."
    )
    parser.add_argument("input", type=Path, help="external exact Gram JSON bundle")
    parser.add_argument("output", type=Path, help="generated .lean file")
    parser.add_argument(
        "--namespace",
        required=True,
        help="generated namespace, beginning with LeanPEP.Imported",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if OUTPUT is absent or differs; do not rewrite it",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        raw = load_json(args.input)
        spec = parse_bundle(raw)
        content = render_module(spec, args.namespace)
        if args.check:
            try:
                existing = args.output.read_text(encoding="utf-8")
            except OSError as exc:
                raise ImportFormatError(
                    f"cannot read generated output {args.output}: {exc}"
                ) from exc
            if existing != content:
                raise ImportFormatError(
                    f"generated output is stale: {args.output}; regenerate it"
                )
        else:
            atomic_write(args.output, content)
        return 0
    except ImportFormatError as exc:
        print(f"import_exact_gram_bundle.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
