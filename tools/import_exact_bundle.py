#!/usr/bin/env python3
"""Generate a Lean module from an exact finite-GD PEP JSON bundle.

The script is intentionally small and dependency-free.  It performs strict
shape/index validation and rejects JSON floating-point numbers.  It is not part
of the trusted proof base: the generated Lean module is checked again by the
Lean-side exact bundle checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Mapping, NoReturn, Sequence

GENERATOR_VERSION = "v0.7.0"
SCHEMA_VERSION = 1
FD = "LeanPEP.Toy.FiniteGD"
_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class ImportFormatError(ValueError):
    """Raised when an external bundle violates the stable input format."""


def fail(path: str, message: str) -> NoReturn:
    raise ImportFormatError(f"{path}: {message}")


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ImportFormatError(f"JSON object contains duplicate key {key!r}")
        result[key] = value
    return result


def require_object(value: Any, path: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        fail(path, "expected an object")
    return value


def require_array(value: Any, path: str) -> Sequence[Any]:
    if not isinstance(value, list):
        fail(path, "expected an array")
    return value


def require_string(value: Any, path: str) -> str:
    if not isinstance(value, str):
        fail(path, "expected a string")
    return value


def require_int(value: Any, path: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(path, "expected an integer; JSON floats are never accepted")
    if minimum is not None and value < minimum:
        fail(path, f"expected an integer >= {minimum}")
    return value


def check_keys(
    obj: Mapping[str, Any],
    path: str,
    *,
    required: Iterable[str],
    optional: Iterable[str] = (),
) -> None:
    required_set = set(required)
    allowed = required_set | set(optional)
    missing = sorted(required_set - obj.keys())
    unknown = sorted(obj.keys() - allowed)
    if missing:
        fail(path, f"missing required field(s): {', '.join(missing)}")
    if unknown:
        fail(path, f"unknown field(s): {', '.join(unknown)}")


def parse_rational(value: Any, path: str) -> Fraction:
    obj = require_object(value, path)
    check_keys(obj, path, required=("num", "den"))
    num = require_int(obj["num"], f"{path}.num")
    den = require_int(obj["den"], f"{path}.den", minimum=1)
    return Fraction(num, den)


@dataclass(frozen=True)
class PointSpec:
    kind: str
    index: int | None = None


@dataclass(frozen=True)
class AffineSpec:
    const: Fraction
    grad: tuple[Fraction, ...]


@dataclass(frozen=True)
class InterpTermSpec:
    weight: Fraction
    i: PointSpec
    j: PointSpec


@dataclass(frozen=True)
class SquareTermSpec:
    weight: Fraction
    form: AffineSpec


@dataclass(frozen=True)
class PrimalSpec:
    grad: tuple[Fraction, ...]
    value: tuple[Fraction, ...]


@dataclass(frozen=True)
class UpperSpec:
    bound: Fraction
    objective: int
    interp_terms: tuple[InterpTermSpec, ...]
    square_terms: tuple[SquareTermSpec, ...]


@dataclass(frozen=True)
class BundleSpec:
    source: str
    steps: int
    declared_point_count: int
    declared_constraint_count: int
    primal: PrimalSpec
    upper: UpperSpec
    expect: str
    source_sha256: str


def parse_point(value: Any, path: str, steps: int) -> PointSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("kind",), optional=("index",))
    kind = require_string(obj["kind"], f"{path}.kind")
    if kind == "star":
        if "index" in obj:
            fail(path, "a star point must not contain an index")
        return PointSpec("star")
    if kind == "iter":
        if "index" not in obj:
            fail(path, "an iter point requires an index")
        index = require_int(obj["index"], f"{path}.index", minimum=0)
        if index > steps:
            fail(f"{path}.index", f"index {index} is outside 0..{steps}")
        return PointSpec("iter", index)
    fail(f"{path}.kind", "expected 'star' or 'iter'")


def parse_rational_vector(
    value: Any, path: str, expected_length: int
) -> tuple[Fraction, ...]:
    items = require_array(value, path)
    if len(items) != expected_length:
        fail(path, f"expected exactly {expected_length} entries, got {len(items)}")
    return tuple(parse_rational(item, f"{path}[{k}]") for k, item in enumerate(items))


def parse_affine(value: Any, path: str, steps: int) -> AffineSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("const", "grad"))
    return AffineSpec(
        const=parse_rational(obj["const"], f"{path}.const"),
        grad=parse_rational_vector(obj["grad"], f"{path}.grad", steps + 1),
    )


def parse_interp_term(value: Any, path: str, steps: int) -> InterpTermSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("weight", "i", "j"))
    return InterpTermSpec(
        weight=parse_rational(obj["weight"], f"{path}.weight"),
        i=parse_point(obj["i"], f"{path}.i", steps),
        j=parse_point(obj["j"], f"{path}.j", steps),
    )


def parse_square_term(value: Any, path: str, steps: int) -> SquareTermSpec:
    obj = require_object(value, path)
    check_keys(obj, path, required=("weight", "form"))
    return SquareTermSpec(
        weight=parse_rational(obj["weight"], f"{path}.weight"),
        form=parse_affine(obj["form"], f"{path}.form", steps),
    )


def canonical_json_sha256(raw: Mapping[str, Any]) -> str:
    canonical = json.dumps(
        raw, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def parse_bundle(raw: Any) -> BundleSpec:
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
            "primal",
            "upper",
        ),
        optional=("expect",),
    )
    schema_version = require_int(obj["schema_version"], "$.schema_version")
    if schema_version != SCHEMA_VERSION:
        fail(
            "$.schema_version",
            f"unsupported schema version {schema_version}; expected {SCHEMA_VERSION}",
        )
    source = require_string(obj["source"], "$.source")
    if not source:
        fail("$.source", "must not be empty")
    steps = require_int(obj["steps"], "$.steps", minimum=0)
    declared_point_count = require_int(
        obj["declared_point_count"], "$.declared_point_count", minimum=0
    )
    declared_constraint_count = require_int(
        obj["declared_constraint_count"],
        "$.declared_constraint_count",
        minimum=0,
    )
    expect = require_string(obj.get("expect", "unchecked"), "$.expect")
    if expect not in {"accepted", "rejected", "unchecked"}:
        fail("$.expect", "expected 'accepted', 'rejected', or 'unchecked'")

    primal_obj = require_object(obj["primal"], "$.primal")
    check_keys(primal_obj, "$.primal", required=("grad", "value"))
    primal = PrimalSpec(
        grad=parse_rational_vector(
            primal_obj["grad"], "$.primal.grad", steps + 1
        ),
        value=parse_rational_vector(
            primal_obj["value"], "$.primal.value", steps + 1
        ),
    )

    upper_obj = require_object(obj["upper"], "$.upper")
    check_keys(
        upper_obj,
        "$.upper",
        required=("bound", "objective", "interp_terms", "square_terms"),
    )
    objective = require_int(
        upper_obj["objective"], "$.upper.objective", minimum=0
    )
    if objective > steps:
        fail(
            "$.upper.objective",
            f"objective index {objective} is outside 0..{steps}",
        )
    interp_items = require_array(upper_obj["interp_terms"], "$.upper.interp_terms")
    square_items = require_array(upper_obj["square_terms"], "$.upper.square_terms")
    upper = UpperSpec(
        bound=parse_rational(upper_obj["bound"], "$.upper.bound"),
        objective=objective,
        interp_terms=tuple(
            parse_interp_term(item, f"$.upper.interp_terms[{k}]", steps)
            for k, item in enumerate(interp_items)
        ),
        square_terms=tuple(
            parse_square_term(item, f"$.upper.square_terms[{k}]", steps)
            for k, item in enumerate(square_items)
        ),
    )

    return BundleSpec(
        source=source,
        steps=steps,
        declared_point_count=declared_point_count,
        declared_constraint_count=declared_constraint_count,
        primal=primal,
        upper=upper,
        expect=expect,
        source_sha256=canonical_json_sha256(obj),
    )


def validate_namespace(namespace: str) -> tuple[str, ...]:
    parts = tuple(namespace.split("."))
    if not parts or any(not _IDENT.fullmatch(part) for part in parts):
        raise ImportFormatError(
            "namespace must be dot-separated ASCII Lean identifiers"
        )
    if parts[:2] != ("LeanPEP", "Imported"):
        raise ImportFormatError(
            "namespace must begin with 'LeanPEP.Imported' for this project"
        )
    return parts


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def lean_rat(value: Fraction) -> str:
    num = value.numerator
    den = value.denominator
    if den == 1:
        return f"({num} : ℚ)"
    return f"(({num} : ℚ) / {den})"


def lean_vector(values: Sequence[Fraction]) -> str:
    return "![" + ", ".join(lean_rat(value) for value in values) + "]"


def lean_point(point: PointSpec, steps: int) -> str:
    if point.kind == "star":
        return f"({FD}.Point.star : {FD}.Point {steps})"
    assert point.index is not None
    return f"{FD}.Point.iter (N := {steps}) {point.index}"


def indent_lines(lines: Sequence[str], spaces: int) -> list[str]:
    prefix = " " * spaces
    return [prefix + line if line else "" for line in lines]


def render_interp_term(term: InterpTermSpec, steps: int) -> list[str]:
    return [
        "{ weight := " + lean_rat(term.weight),
        "  i := " + lean_point(term.i, steps),
        "  j := " + lean_point(term.j, steps) + " }",
    ]


def render_square_term(term: SquareTermSpec) -> list[str]:
    return [
        "{ weight := " + lean_rat(term.weight),
        "  form :=",
        "    { constCoeff := " + lean_rat(term.form.const),
        "      gradCoeff := " + lean_vector(term.form.grad) + " } }",
    ]


def render_record_list(
    items: Sequence[Any], renderer: Any, *, steps: int | None = None
) -> list[str]:
    if not items:
        return ["[]"]
    lines: list[str] = ["["]
    for index, item in enumerate(items):
        rendered = renderer(item, steps) if steps is not None else renderer(item)
        suffix = "," if index + 1 < len(items) else ""
        rendered[-1] += suffix
        lines.extend(indent_lines(rendered, 2))
    lines.append("]")
    return lines


def render_namespace_open(parts: Sequence[str]) -> list[str]:
    lines: list[str] = []
    for part in parts:
        lines.append(f"namespace {part}")
    return lines


def render_namespace_close(parts: Sequence[str]) -> list[str]:
    return [f"end {part}" for part in reversed(parts)]


def render_module(spec: BundleSpec, namespace: str) -> str:
    ns_parts = validate_namespace(namespace)
    n = spec.steps
    interp_lines = render_record_list(
        spec.upper.interp_terms, render_interp_term, steps=n
    )
    square_lines = render_record_list(spec.upper.square_terms, render_square_term)

    lines: list[str] = [
        f"import {FD}.ExternalBundle",
        "",
        "/-!",
        "This file is generated by `tools/import_exact_bundle.py`.",
        "Do not edit it by hand; regenerate it from the exact JSON source.",
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
            f"def metadataQ : {FD}.ImportMetadataQ {n} :=",
            f"  {{ schemaVersion := {SCHEMA_VERSION}",
            f"    declaredSteps := {n}",
            f"    declaredPointCount := {spec.declared_point_count}",
            f"    declaredConstraintCount := {spec.declared_constraint_count}",
            f"    sourceName := {lean_string(spec.source)}",
            f"    sourceSha256 := {lean_string(spec.source_sha256)}",
            f"    generatorVersion := {lean_string(GENERATOR_VERSION)} }}",
            "",
            f"def primalQ : {FD}.DataQ {n} :=",
            f"  {{ grad := {lean_vector(spec.primal.grad)}",
            f"    value := {lean_vector(spec.primal.value)} }}",
            "",
            f"def upperCertQ : {FD}.UpperCertQ {n} :=",
            f"  {{ bound := {lean_rat(spec.upper.bound)}",
            f"    objective := {spec.upper.objective}",
            "    interpTerms :=",
        ]
    )
    lines.extend(indent_lines(interp_lines, 6))
    lines.append("    squareTerms :=")
    lines.extend(indent_lines(square_lines, 6))
    lines.append("  }")
    lines.extend(
        [
            "",
            f"def bundleQ : {FD}.ExactBundleQ {n} :=",
            "  { metadata := metadataQ",
            "    primal := primalQ",
            "    upper := upperCertQ }",
            "",
        ]
    )

    if spec.expect == "accepted":
        lines.extend(
            [
                "theorem bundleQ_check :",
                f"    {FD}.checkExactBundleQ bundleQ = true := by",
                "  native_decide",
                "",
                "theorem bundleQ_sound_real :",
                f"    {FD}.checkImportMetadataQ metadataQ = true ∧",
                f"      {FD}.Feasible ({FD}.toRealData primalQ) ∧",
                "      primalQ.value upperCertQ.objective = upperCertQ.bound ∧",
                f"      ∀ d : {FD}.DataR {n},",
                f"        {FD}.Feasible d →",
                "          d.value upperCertQ.objective ≤ (upperCertQ.bound : ℝ) := by",
                "  simpa [bundleQ] using",
                f"    {FD}.checkExactBundleQ_sound_real bundleQ bundleQ_check",
                "",
            ]
        )
    elif spec.expect == "rejected":
        lines.extend(
            [
                "theorem bundleQ_rejected :",
                f"    {FD}.checkExactBundleQ bundleQ = false := by",
                "  native_decide",
                "",
            ]
        )

    lines.extend(render_namespace_close(ns_parts))
    lines.append("")
    return "\n".join(lines)


def load_json(path: Path) -> Mapping[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle, object_pairs_hook=reject_duplicate_pairs)
    except OSError as exc:
        raise ImportFormatError(f"cannot read {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ImportFormatError(
            f"invalid JSON at line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc


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


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate an exact Lean PEP bundle module from strict JSON."
    )
    parser.add_argument("input", type=Path, help="external JSON bundle")
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
        print(f"import_exact_bundle.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
