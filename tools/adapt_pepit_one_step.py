#!/usr/bin/env python3
"""Adapt one concrete PEPit one-step GD solver artifact to Lean-PEP.

The source boundary in this file is intentionally narrower than the generic
``external-gram-format-v1`` boundary.  It describes the concrete PEPit model

    SmoothConvexFunction(L=1),
    x1 = x0 - grad f(x0),
    ||x0 - x_*||^2 <= 1,
    maximize f(x1) - f(x_*).

The adapter validates PEPit's discrete orderings and exact symbolic coefficient
arrays against an independently reconstructed template, transforms the solver's
leaf-point Gram matrix to the centered basis ``[x0-x*, g0, g1]``, and emits an
ordinary ``approximate-gram-format-v1`` artifact.  That artifact then follows
the already verified raw/reconstructed Gram audit pipeline.

This adapter, the PEPit exporter, and all numerical factor reconstruction are
untrusted.  Lean independently rechecks the adapted mathematical bundles.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

import import_exact_bundle as base
import import_exact_gram_bundle as exact
import prepare_approx_bundle as approx

SOURCE_SCHEMA_VERSION = 1
ADAPTER_REPORT_VERSION = 1
ADAPTER_GENERATOR_VERSION = "v0.11.4"
ADAPTER_ID = "pepit-smooth-convex-gd-one-step-v1"
PEPIT_COMMIT = "5a061a1b2dbe450b6bac42e2442942748f3b1f32"
PEPIT_FUNCTION_CLASS = "SmoothConvexFunction"
EXPECTED_POINT_ORDER = ("star", "x0", "x1")
EXPECTED_VALUE_ORDER = ("f_star", "f0", "f1")
EXPECTED_LEAF_ORDER = ("x_star", "x0", "g0", "g1")
EXPECTED_CONSTRAINT_ORDER = (
    "initial_radius",
    "smooth_convexity:star:x0",
    "smooth_convexity:star:x1",
    "smooth_convexity:x0:star",
    "smooth_convexity:x0:x1",
    "smooth_convexity:x1:star",
    "smooth_convexity:x1:x0",
)
TARGET_POINT_ORDER = ("star", "x0", "x1")
TARGET_GRAM_BASIS = ("x0_minus_xstar", "g0", "g1")

AdapterFormatError = approx.ApproxFormatError


def fail(path: str, message: str) -> NoReturn:
    raise AdapterFormatError(f"{path}: {message}")


def require_object(value: Any, path: str) -> Mapping[str, Any]:
    try:
        return exact.require_object(value, path)
    except exact.ImportFormatError as exc:
        raise AdapterFormatError(str(exc)) from exc


def require_array(value: Any, path: str) -> Sequence[Any]:
    try:
        return exact.require_array(value, path)
    except exact.ImportFormatError as exc:
        raise AdapterFormatError(str(exc)) from exc


def require_string(value: Any, path: str) -> str:
    try:
        return exact.require_string(value, path)
    except exact.ImportFormatError as exc:
        raise AdapterFormatError(str(exc)) from exc


def require_int(value: Any, path: str, *, minimum: int | None = None) -> int:
    try:
        return exact.require_int(value, path, minimum=minimum)
    except exact.ImportFormatError as exc:
        raise AdapterFormatError(str(exc)) from exc


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
        raise AdapterFormatError(str(exc)) from exc


def parse_decimal(value: Any, path: str) -> tuple[str, Fraction]:
    return approx.parse_decimal_string(value, path)


def parse_decimal_vector(
    value: Any, path: str, expected_length: int
) -> tuple[tuple[str, Fraction], ...]:
    items = require_array(value, path)
    if len(items) != expected_length:
        fail(path, f"expected exactly {expected_length} entries, got {len(items)}")
    return tuple(parse_decimal(item, f"{path}[{k}]") for k, item in enumerate(items))


def parse_decimal_matrix(
    value: Any, path: str, rows: int, cols: int
) -> tuple[tuple[tuple[str, Fraction], ...], ...]:
    items = require_array(value, path)
    if len(items) != rows:
        fail(path, f"expected exactly {rows} rows, got {len(items)}")
    return tuple(
        parse_decimal_vector(row, f"{path}[{i}]", cols)
        for i, row in enumerate(items)
    )


def fractions_vector(parsed: Sequence[tuple[str, Fraction]]) -> tuple[Fraction, ...]:
    return tuple(value for _, value in parsed)


def fractions_matrix(
    parsed: Sequence[Sequence[tuple[str, Fraction]]],
) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(tuple(value for _, value in row) for row in parsed)


def decimal_string(value: Fraction) -> str:
    """Render an exact rational with a terminating base-10 expansion."""

    if value == 0:
        return "0"
    sign = "-" if value < 0 else ""
    numerator = abs(value.numerator)
    denominator = value.denominator
    twos = 0
    fives = 0
    while denominator % 2 == 0:
        denominator //= 2
        twos += 1
    while denominator % 5 == 0:
        denominator //= 5
        fives += 1
    if denominator != 1:
        raise AdapterFormatError(
            f"cannot render non-terminating rational {value} as an approximate decimal string"
        )
    scale = max(twos, fives)
    numerator *= 2 ** (scale - twos)
    numerator *= 5 ** (scale - fives)
    if scale == 0:
        return sign + str(numerator)
    digits = str(numerator).rjust(scale + 1, "0")
    whole = digits[:-scale]
    fractional = digits[-scale:].rstrip("0")
    if not fractional:
        return sign + whole
    return sign + whole + "." + fractional


def zero_vector(n: int) -> tuple[Fraction, ...]:
    return tuple(Fraction(0) for _ in range(n))


def zero_matrix(rows: int, cols: int) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(zero_vector(cols) for _ in range(rows))


def identity_matrix(n: int) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(
        tuple(Fraction(int(i == j)) for j in range(n)) for i in range(n)
    )


def vector_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> tuple[Fraction, ...]:
    if len(a) != len(b):
        raise ValueError("vector dimension mismatch")
    return tuple(x + y for x, y in zip(a, b, strict=True))


def vector_sub(a: Sequence[Fraction], b: Sequence[Fraction]) -> tuple[Fraction, ...]:
    if len(a) != len(b):
        raise ValueError("vector dimension mismatch")
    return tuple(x - y for x, y in zip(a, b, strict=True))


def vector_scale(c: Fraction, a: Sequence[Fraction]) -> tuple[Fraction, ...]:
    return tuple(c * x for x in a)


def matrix_add(
    a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]
) -> tuple[tuple[Fraction, ...], ...]:
    if len(a) != len(b) or any(len(x) != len(y) for x, y in zip(a, b, strict=True)):
        raise ValueError("matrix dimension mismatch")
    return tuple(
        tuple(x + y for x, y in zip(row_a, row_b, strict=True))
        for row_a, row_b in zip(a, b, strict=True)
    )


def matrix_scale(
    c: Fraction, a: Sequence[Sequence[Fraction]]
) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(tuple(c * x for x in row) for row in a)


def transpose(a: Sequence[Sequence[Fraction]]) -> tuple[tuple[Fraction, ...], ...]:
    if not a:
        return tuple()
    cols = len(a[0])
    if any(len(row) != cols for row in a):
        raise ValueError("ragged matrix")
    return tuple(tuple(a[i][j] for i in range(len(a))) for j in range(cols))


def matrix_mul(
    a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]
) -> tuple[tuple[Fraction, ...], ...]:
    if not a or not b:
        return tuple()
    inner = len(a[0])
    if any(len(row) != inner for row in a):
        raise ValueError("ragged left matrix")
    if len(b) != inner:
        raise ValueError("matrix multiplication dimension mismatch")
    cols = len(b[0])
    if any(len(row) != cols for row in b):
        raise ValueError("ragged right matrix")
    return tuple(
        tuple(
            sum((a[i][k] * b[k][j] for k in range(inner)), Fraction(0))
            for j in range(cols)
        )
        for i in range(len(a))
    )


def matrix_vector_mul(
    a: Sequence[Sequence[Fraction]], x: Sequence[Fraction]
) -> tuple[Fraction, ...]:
    if any(len(row) != len(x) for row in a):
        raise ValueError("matrix/vector dimension mismatch")
    return tuple(
        sum((entry * value for entry, value in zip(row, x, strict=True)), Fraction(0))
        for row in a
    )


def outer(a: Sequence[Fraction], b: Sequence[Fraction]) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(tuple(x * y for y in b) for x in a)


def sym_outer(a: Sequence[Fraction], b: Sequence[Fraction]) -> tuple[tuple[Fraction, ...], ...]:
    return matrix_scale(Fraction(1, 2), matrix_add(outer(a, b), outer(b, a)))


def matrix_equal(a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]) -> bool:
    return tuple(tuple(row) for row in a) == tuple(tuple(row) for row in b)


def rational_json(value: Fraction) -> dict[str, int]:
    return {"num": value.numerator, "den": value.denominator}


def rational_vector_json(values: Sequence[Fraction]) -> list[dict[str, int]]:
    return [rational_json(value) for value in values]


def rational_matrix_json(
    rows: Sequence[Sequence[Fraction]],
) -> list[list[dict[str, int]]]:
    return [rational_vector_json(row) for row in rows]


def decimal_vector_json(values: Sequence[Fraction]) -> list[str]:
    return [decimal_string(value) for value in values]


def decimal_matrix_json(rows: Sequence[Sequence[Fraction]]) -> list[list[str]]:
    return [decimal_vector_json(row) for row in rows]


@dataclass(frozen=True)
class LinearExpr:
    const: Fraction
    value_coeff: tuple[Fraction, ...]
    gram_coeff: tuple[tuple[Fraction, ...], ...]

    def neg(self) -> "LinearExpr":
        return LinearExpr(
            const=-self.const,
            value_coeff=vector_scale(Fraction(-1), self.value_coeff),
            gram_coeff=matrix_scale(Fraction(-1), self.gram_coeff),
        )


@dataclass(frozen=True)
class ConstraintSpec:
    label: str
    kind: str
    sense: str
    i: int | None
    j: int | None
    expr: LinearExpr
    dual_source: str
    dual: Fraction


@dataclass(frozen=True)
class Factor:
    weight_source: str
    weight: Fraction
    vector_sources: tuple[str, ...]
    vector: tuple[Fraction, ...]


@dataclass(frozen=True)
class SourceArtifact:
    raw: Mapping[str, Any]
    source_sha256: str
    producer: Mapping[str, str]
    capture_mode: str
    adapter_id: str
    function_class: str
    smoothness_source: str
    smoothness: Fraction
    step_size_source: str
    step_size: Fraction
    steps: int
    point_order: tuple[str, ...]
    value_order: tuple[str, ...]
    leaf_order: tuple[str, ...]
    point_decomposition: tuple[tuple[Fraction, ...], ...]
    gradient_decomposition: tuple[tuple[Fraction, ...], ...]
    constraints: tuple[ConstraintSpec, ...]
    constraint_order: tuple[str, ...]
    objective: LinearExpr
    declared_model_fingerprint: str
    primal_gram_sources: tuple[tuple[str, ...], ...]
    primal_gram: tuple[tuple[Fraction, ...], ...]
    function_value_sources: tuple[str, ...]
    function_values: tuple[Fraction, ...]
    dual_residual_sources: tuple[tuple[str, ...], ...]
    dual_residual: tuple[tuple[Fraction, ...], ...]
    primal_objective_source: str
    primal_objective: Fraction
    dual_objective_source: str
    dual_objective: Fraction
    primal_factors: tuple[Factor, ...]
    dual_factors: tuple[Factor, ...]
    policy: Mapping[str, Any]
    expect_adapter: str
    expect_raw: str
    expect_reconstructed: str


def parse_labels(value: Any, path: str) -> tuple[str, ...]:
    try:
        return exact.parse_labels(value, path)
    except exact.ImportFormatError as exc:
        raise AdapterFormatError(str(exc)) from exc


def parse_linear_expr(value: Any, path: str, p: int, n: int) -> LinearExpr:
    obj = require_object(value, path)
    check_keys(obj, path, required=("const", "value_coeff", "gram_coeff"))
    _, const = parse_decimal(obj["const"], f"{path}.const")
    value_coeff = fractions_vector(
        parse_decimal_vector(obj["value_coeff"], f"{path}.value_coeff", p)
    )
    gram_coeff = fractions_matrix(
        parse_decimal_matrix(obj["gram_coeff"], f"{path}.gram_coeff", n, n)
    )
    return LinearExpr(const, value_coeff, gram_coeff)


def parse_factor_cert(value: Any, path: str, n: int) -> tuple[Factor, ...]:
    obj = require_object(value, path)
    check_keys(obj, path, required=("factors",), optional=("source", "method"))
    items = require_array(obj["factors"], f"{path}.factors")
    factors: list[Factor] = []
    for k, item in enumerate(items):
        item_path = f"{path}.factors[{k}]"
        fobj = require_object(item, item_path)
        check_keys(fobj, item_path, required=("weight", "vector"))
        weight_source, weight = parse_decimal(fobj["weight"], f"{item_path}.weight")
        parsed_vector = parse_decimal_vector(
            fobj["vector"], f"{item_path}.vector", n
        )
        factors.append(
            Factor(
                weight_source=weight_source,
                weight=weight,
                vector_sources=tuple(source for source, _ in parsed_vector),
                vector=fractions_vector(parsed_vector),
            )
        )
    return tuple(factors)


def parse_expect(value: Any, path: str) -> tuple[str, str, str]:
    if value is None:
        return ("unchecked", "unchecked", "unchecked")
    obj = require_object(value, path)
    check_keys(obj, path, required=("adapter", "raw", "reconstructed"))
    outputs: list[str] = []
    for field in ("adapter", "raw", "reconstructed"):
        result = require_string(obj[field], f"{path}.{field}")
        if result not in {"accepted", "rejected", "unchecked"}:
            fail(f"{path}.{field}", "expected accepted, rejected, or unchecked")
        outputs.append(result)
    return tuple(outputs)  # type: ignore[return-value]


def parse_source(raw: Any) -> SourceArtifact:
    obj = require_object(raw, "$")
    check_keys(
        obj,
        "$",
        required=(
            "schema_version",
            "producer",
            "problem",
            "solver_output",
            "factorization_hints",
            "reconstruction_policy",
        ),
        optional=("expect",),
    )
    schema = require_int(obj["schema_version"], "$.schema_version")
    if schema != SOURCE_SCHEMA_VERSION:
        fail(
            "$.schema_version",
            f"unsupported schema version {schema}; expected {SOURCE_SCHEMA_VERSION}",
        )

    producer_obj = require_object(obj["producer"], "$.producer")
    check_keys(
        producer_obj,
        "$.producer",
        required=(
            "name",
            "package_version",
            "git_commit",
            "wrapper",
            "solver",
            "solver_status",
            "capture_mode",
        ),
    )
    producer = {
        field: require_string(producer_obj[field], f"$.producer.{field}")
        for field in (
            "name",
            "package_version",
            "git_commit",
            "wrapper",
            "solver",
            "solver_status",
            "capture_mode",
        )
    }
    capture_mode = producer["capture_mode"]
    if capture_mode not in {"live_pepit", "deterministic_regression_fixture"}:
        fail(
            "$.producer.capture_mode",
            "expected live_pepit or deterministic_regression_fixture",
        )

    problem_obj = require_object(obj["problem"], "$.problem")
    check_keys(
        problem_obj,
        "$.problem",
        required=(
            "adapter_id",
            "function_class",
            "smoothness",
            "step_size",
            "steps",
            "point_order",
            "function_value_order",
            "leaf_point_order",
            "point_decomposition",
            "gradient_decomposition",
            "constraints",
            "objective",
            "model_fingerprint",
        ),
    )
    adapter_id = require_string(problem_obj["adapter_id"], "$.problem.adapter_id")
    function_class = require_string(
        problem_obj["function_class"], "$.problem.function_class"
    )
    smoothness_source, smoothness = parse_decimal(
        problem_obj["smoothness"], "$.problem.smoothness"
    )
    step_size_source, step_size = parse_decimal(
        problem_obj["step_size"], "$.problem.step_size"
    )
    steps = require_int(problem_obj["steps"], "$.problem.steps", minimum=0)
    point_order = parse_labels(problem_obj["point_order"], "$.problem.point_order")
    value_order = parse_labels(
        problem_obj["function_value_order"], "$.problem.function_value_order"
    )
    leaf_order = parse_labels(
        problem_obj["leaf_point_order"], "$.problem.leaf_point_order"
    )
    p = len(point_order)
    n = len(leaf_order)
    if len(value_order) != p:
        fail(
            "$.problem.function_value_order",
            f"expected {p} labels to match point_order, got {len(value_order)}",
        )
    point_decomposition = fractions_matrix(
        parse_decimal_matrix(
            problem_obj["point_decomposition"],
            "$.problem.point_decomposition",
            p,
            n,
        )
    )
    gradient_decomposition = fractions_matrix(
        parse_decimal_matrix(
            problem_obj["gradient_decomposition"],
            "$.problem.gradient_decomposition",
            p,
            n,
        )
    )

    constraint_items = require_array(problem_obj["constraints"], "$.problem.constraints")
    constraints: list[ConstraintSpec] = []
    labels: set[str] = set()
    for k, item in enumerate(constraint_items):
        item_path = f"$.problem.constraints[{k}]"
        cobj = require_object(item, item_path)
        check_keys(
            cobj,
            item_path,
            required=("label", "kind", "sense", "expr", "dual"),
            optional=("i", "j"),
        )
        label = require_string(cobj["label"], f"{item_path}.label")
        if not label:
            fail(f"{item_path}.label", "must not be empty")
        if label in labels:
            fail(f"{item_path}.label", f"duplicate constraint label {label!r}")
        labels.add(label)
        kind = require_string(cobj["kind"], f"{item_path}.kind")
        sense = require_string(cobj["sense"], f"{item_path}.sense")
        if kind not in {"initial", "interpolation"}:
            fail(f"{item_path}.kind", "expected initial or interpolation")
        if sense != "le":
            fail(f"{item_path}.sense", "PEPit Constraint.expression must be encoded as <= 0")
        i: int | None = None
        j: int | None = None
        if kind == "interpolation":
            if "i" not in cobj or "j" not in cobj:
                fail(item_path, "interpolation constraints require i and j")
            i = require_int(cobj["i"], f"{item_path}.i", minimum=0)
            j = require_int(cobj["j"], f"{item_path}.j", minimum=0)
            if i >= p or j >= p:
                fail(item_path, f"interpolation pair ({i},{j}) is outside 0..{p - 1}")
            if i == j:
                fail(item_path, "PEPit omits diagonal interpolation constraints")
        elif "i" in cobj or "j" in cobj:
            fail(item_path, "initial constraints must not contain i or j")
        dual_source, dual = parse_decimal(cobj["dual"], f"{item_path}.dual")
        constraints.append(
            ConstraintSpec(
                label=label,
                kind=kind,
                sense=sense,
                i=i,
                j=j,
                expr=parse_linear_expr(cobj["expr"], f"{item_path}.expr", p, n),
                dual_source=dual_source,
                dual=dual,
            )
        )
    constraint_order = tuple(c.label for c in constraints)
    objective = parse_linear_expr(problem_obj["objective"], "$.problem.objective", p, n)
    declared_model_fingerprint = require_string(
        problem_obj["model_fingerprint"], "$.problem.model_fingerprint"
    )

    solver_obj = require_object(obj["solver_output"], "$.solver_output")
    check_keys(
        solver_obj,
        "$.solver_output",
        required=(
            "primal_gram",
            "function_values",
            "dual_residual",
            "primal_objective",
            "dual_objective",
        ),
    )
    parsed_gram = parse_decimal_matrix(
        solver_obj["primal_gram"], "$.solver_output.primal_gram", n, n
    )
    parsed_values = parse_decimal_vector(
        solver_obj["function_values"], "$.solver_output.function_values", p
    )
    parsed_residual = parse_decimal_matrix(
        solver_obj["dual_residual"], "$.solver_output.dual_residual", n, n
    )
    primal_objective_source, primal_objective = parse_decimal(
        solver_obj["primal_objective"], "$.solver_output.primal_objective"
    )
    dual_objective_source, dual_objective = parse_decimal(
        solver_obj["dual_objective"], "$.solver_output.dual_objective"
    )

    hints_obj = require_object(obj["factorization_hints"], "$.factorization_hints")
    check_keys(
        hints_obj,
        "$.factorization_hints",
        required=("primal_gram", "dual_residual"),
        optional=("source",),
    )
    primal_factors = parse_factor_cert(
        hints_obj["primal_gram"], "$.factorization_hints.primal_gram", n
    )
    dual_factors = parse_factor_cert(
        hints_obj["dual_residual"], "$.factorization_hints.dual_residual", n
    )

    policy_obj = require_object(obj["reconstruction_policy"], "$.reconstruction_policy")
    check_keys(
        policy_obj,
        "$.reconstruction_policy",
        required=("method", "max_denominator", "max_abs_error"),
    )
    # Reuse the exact policy validator now so malformed JSON floats, methods,
    # and bounds are rejected at this boundary.
    approx.parse_policy(policy_obj, "$.reconstruction_policy")

    expect_adapter, expect_raw, expect_reconstructed = parse_expect(
        obj.get("expect"), "$.expect"
    )

    return SourceArtifact(
        raw=obj,
        source_sha256=base.canonical_json_sha256(obj),
        producer=producer,
        capture_mode=capture_mode,
        adapter_id=adapter_id,
        function_class=function_class,
        smoothness_source=smoothness_source,
        smoothness=smoothness,
        step_size_source=step_size_source,
        step_size=step_size,
        steps=steps,
        point_order=point_order,
        value_order=value_order,
        leaf_order=leaf_order,
        point_decomposition=point_decomposition,
        gradient_decomposition=gradient_decomposition,
        constraints=tuple(constraints),
        constraint_order=constraint_order,
        objective=objective,
        declared_model_fingerprint=declared_model_fingerprint,
        primal_gram_sources=tuple(tuple(source for source, _ in row) for row in parsed_gram),
        primal_gram=fractions_matrix(parsed_gram),
        function_value_sources=tuple(source for source, _ in parsed_values),
        function_values=fractions_vector(parsed_values),
        dual_residual_sources=tuple(tuple(source for source, _ in row) for row in parsed_residual),
        dual_residual=fractions_matrix(parsed_residual),
        primal_objective_source=primal_objective_source,
        primal_objective=primal_objective,
        dual_objective_source=dual_objective_source,
        dual_objective=dual_objective,
        primal_factors=primal_factors,
        dual_factors=dual_factors,
        policy={
            "method": require_string(policy_obj["method"], "$.reconstruction_policy.method"),
            "max_denominator": require_int(
                policy_obj["max_denominator"],
                "$.reconstruction_policy.max_denominator",
                minimum=1,
            ),
            "max_abs_error": require_string(
                policy_obj["max_abs_error"],
                "$.reconstruction_policy.max_abs_error",
            ),
        },
        expect_adapter=expect_adapter,
        expect_raw=expect_raw,
        expect_reconstructed=expect_reconstructed,
    )


def expected_model() -> tuple[
    tuple[tuple[Fraction, ...], ...],
    tuple[tuple[Fraction, ...], ...],
    tuple[ConstraintSpec, ...],
    LinearExpr,
]:
    n = len(EXPECTED_LEAF_ORDER)
    e = identity_matrix(n)
    x_star = e[0]
    x0 = e[1]
    g0 = e[2]
    g1 = e[3]
    x1 = vector_sub(x0, g0)
    points = (x_star, x0, x1)
    gradients = (zero_vector(n), g0, g1)

    initial_direction = vector_sub(x0, x_star)
    initial_expr = LinearExpr(
        const=Fraction(-1),
        value_coeff=zero_vector(3),
        gram_coeff=outer(initial_direction, initial_direction),
    )
    constraints: list[ConstraintSpec] = [
        ConstraintSpec(
            label="initial_radius",
            kind="initial",
            sense="le",
            i=None,
            j=None,
            expr=initial_expr,
            dual_source="0",
            dual=Fraction(0),
        )
    ]
    point_labels = EXPECTED_POINT_ORDER
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            value_coeff = [Fraction(0), Fraction(0), Fraction(0)]
            value_coeff[j] += 1
            value_coeff[i] -= 1
            direction = vector_sub(points[i], points[j])
            grad_diff = vector_sub(gradients[i], gradients[j])
            gram_coeff = matrix_add(
                sym_outer(gradients[j], direction),
                matrix_scale(Fraction(1, 2), outer(grad_diff, grad_diff)),
            )
            constraints.append(
                ConstraintSpec(
                    label=f"smooth_convexity:{point_labels[i]}:{point_labels[j]}",
                    kind="interpolation",
                    sense="le",
                    i=i,
                    j=j,
                    expr=LinearExpr(Fraction(0), tuple(value_coeff), gram_coeff),
                    dual_source="0",
                    dual=Fraction(0),
                )
            )
    objective = LinearExpr(
        const=Fraction(0),
        value_coeff=(Fraction(-1), Fraction(0), Fraction(1)),
        gram_coeff=zero_matrix(n, n),
    )
    return points, gradients, tuple(constraints), objective


def normalized_expr_json(expr: LinearExpr) -> Mapping[str, Any]:
    return {
        "const": rational_json(expr.const),
        "value_coeff": rational_vector_json(expr.value_coeff),
        "gram_coeff": rational_matrix_json(expr.gram_coeff),
    }


def model_fingerprint_payload(
    *,
    adapter_id: str,
    function_class: str,
    smoothness: Fraction,
    step_size: Fraction,
    steps: int,
    point_order: Sequence[str],
    value_order: Sequence[str],
    leaf_order: Sequence[str],
    point_decomposition: Sequence[Sequence[Fraction]],
    gradient_decomposition: Sequence[Sequence[Fraction]],
    constraints: Sequence[ConstraintSpec],
    objective: LinearExpr,
) -> Mapping[str, Any]:
    return {
        "adapter_id": adapter_id,
        "function_class": function_class,
        "smoothness": rational_json(smoothness),
        "step_size": rational_json(step_size),
        "steps": steps,
        "point_order": list(point_order),
        "function_value_order": list(value_order),
        "leaf_point_order": list(leaf_order),
        "point_decomposition": rational_matrix_json(point_decomposition),
        "gradient_decomposition": rational_matrix_json(gradient_decomposition),
        "constraints": [
            {
                "label": c.label,
                "kind": c.kind,
                "sense": c.sense,
                **({"i": c.i, "j": c.j} if c.kind == "interpolation" else {}),
                "expr": normalized_expr_json(c.expr),
            }
            for c in constraints
        ],
        "objective": normalized_expr_json(objective),
    }


def fingerprint(payload: Mapping[str, Any]) -> str:
    return base.canonical_json_sha256(payload)


def expected_model_fingerprint() -> str:
    points, gradients, constraints, objective = expected_model()
    return fingerprint(
        model_fingerprint_payload(
            adapter_id=ADAPTER_ID,
            function_class=PEPIT_FUNCTION_CLASS,
            smoothness=Fraction(1),
            step_size=Fraction(1),
            steps=1,
            point_order=EXPECTED_POINT_ORDER,
            value_order=EXPECTED_VALUE_ORDER,
            leaf_order=EXPECTED_LEAF_ORDER,
            point_decomposition=points,
            gradient_decomposition=gradients,
            constraints=constraints,
            objective=objective,
        )
    )


def source_model_fingerprint(source: SourceArtifact) -> str:
    return fingerprint(
        model_fingerprint_payload(
            adapter_id=source.adapter_id,
            function_class=source.function_class,
            smoothness=source.smoothness,
            step_size=source.step_size,
            steps=source.steps,
            point_order=source.point_order,
            value_order=source.value_order,
            leaf_order=source.leaf_order,
            point_decomposition=source.point_decomposition,
            gradient_decomposition=source.gradient_decomposition,
            constraints=source.constraints,
            objective=source.objective,
        )
    )


def factor_matrix(factors: Sequence[Factor]) -> tuple[tuple[Fraction, ...], ...]:
    if not factors:
        return tuple()
    n = len(factors[0].vector)
    result = zero_matrix(n, n)
    for factor in factors:
        result = matrix_add(
            result,
            matrix_scale(factor.weight, outer(factor.vector, factor.vector)),
        )
    return result


def mismatch(field: str, expected: Any, actual: Any) -> Mapping[str, Any]:
    return {"field": field, "expected": expected, "actual": actual}


def compare_source(source: SourceArtifact) -> tuple[list[Mapping[str, Any]], str, str]:
    expected_points, expected_gradients, expected_constraints, expected_objective = expected_model()
    expected_fp = expected_model_fingerprint()
    computed_fp = source_model_fingerprint(source)
    mismatches: list[Mapping[str, Any]] = []

    scalar_checks = (
        ("producer.name", "PEPit", source.producer["name"]),
        ("producer.git_commit", PEPIT_COMMIT, source.producer["git_commit"]),
        ("problem.adapter_id", ADAPTER_ID, source.adapter_id),
        ("problem.function_class", PEPIT_FUNCTION_CLASS, source.function_class),
        ("problem.smoothness", rational_json(Fraction(1)), rational_json(source.smoothness)),
        ("problem.step_size", rational_json(Fraction(1)), rational_json(source.step_size)),
        ("problem.steps", 1, source.steps),
        ("problem.point_order", list(EXPECTED_POINT_ORDER), list(source.point_order)),
        ("problem.function_value_order", list(EXPECTED_VALUE_ORDER), list(source.value_order)),
        ("problem.leaf_point_order", list(EXPECTED_LEAF_ORDER), list(source.leaf_order)),
        ("problem.constraint_order", list(EXPECTED_CONSTRAINT_ORDER), list(source.constraint_order)),
        ("problem.point_decomposition", rational_matrix_json(expected_points), rational_matrix_json(source.point_decomposition)),
        ("problem.gradient_decomposition", rational_matrix_json(expected_gradients), rational_matrix_json(source.gradient_decomposition)),
        ("problem.objective", normalized_expr_json(expected_objective), normalized_expr_json(source.objective)),
        ("problem.model_fingerprint.declared", expected_fp, source.declared_model_fingerprint),
        ("problem.model_fingerprint.computed", expected_fp, computed_fp),
    )
    for field, expected, actual in scalar_checks:
        if expected != actual:
            mismatches.append(mismatch(field, expected, actual))

    expected_by_label = {item.label: item for item in expected_constraints}
    source_by_label = {item.label: item for item in source.constraints}
    if set(expected_by_label) != set(source_by_label):
        mismatches.append(
            mismatch(
                "problem.constraint_labels",
                sorted(expected_by_label),
                sorted(source_by_label),
            )
        )
    for label in sorted(set(expected_by_label) & set(source_by_label)):
        e = expected_by_label[label]
        a = source_by_label[label]
        expected_record = {
            "kind": e.kind,
            "sense": e.sense,
            "i": e.i,
            "j": e.j,
            "expr": normalized_expr_json(e.expr),
        }
        actual_record = {
            "kind": a.kind,
            "sense": a.sense,
            "i": a.i,
            "j": a.j,
            "expr": normalized_expr_json(a.expr),
        }
        if expected_record != actual_record:
            mismatches.append(
                mismatch(f"problem.constraints[{label}]", expected_record, actual_record)
            )

    # Factorization hints are candidate numerical postprocessing, not part of
    # PEPit's symbolic formulation.  Their exact validity is checked downstream
    # by the existing raw/reconstructed Gram auditor and is reported separately
    # below; it must not change formulation-adapter acceptance.
    return mismatches, expected_fp, computed_fp


def build_basis_maps(source: SourceArtifact) -> tuple[
    tuple[tuple[Fraction, ...], ...],
    tuple[tuple[Fraction, ...], ...],
]:
    if set(source.leaf_order) != set(EXPECTED_LEAF_ORDER):
        fail(
            "$.problem.leaf_point_order",
            "adapter requires exactly x_star, x0, g0, g1 labels even when their order is being audited",
        )
    index = {label: k for k, label in enumerate(source.leaf_order)}
    n = len(source.leaf_order)
    c = [[Fraction(0) for _ in range(3)] for _ in range(n)]
    c[index["x_star"]][0] = -1
    c[index["x0"]][0] = 1
    c[index["g0"]][1] = 1
    c[index["g1"]][2] = 1
    l = [[Fraction(0) for _ in range(n)] for _ in range(3)]
    l[0][index["x0"]] = 1
    l[1][index["g0"]] = 1
    l[2][index["g1"]] = 1
    c_t = tuple(tuple(row) for row in c)
    l_t = tuple(tuple(row) for row in l)
    if matrix_mul(l_t, c_t) != identity_matrix(3):
        raise AssertionError("internal centered-basis left inverse is invalid")
    return c_t, l_t


def transform_expr_to_target(
    expr: LinearExpr,
    source: SourceArtifact,
    l: Sequence[Sequence[Fraction]],
) -> LinearExpr:
    value_index = {label: k for k, label in enumerate(source.value_order)}
    value_coeff = tuple(expr.value_coeff[value_index[label]] for label in EXPECTED_VALUE_ORDER)
    gram_coeff = matrix_mul(matrix_mul(l, expr.gram_coeff), transpose(l))
    return LinearExpr(expr.const, value_coeff, gram_coeff)


def transform_factor_primal(
    factor: Factor, c: Sequence[Sequence[Fraction]]
) -> Mapping[str, Any]:
    target = matrix_vector_mul(transpose(c), factor.vector)
    return {
        "weight": factor.weight_source,
        "vector": decimal_vector_json(target),
    }


def transform_factor_dual(
    factor: Factor,
    c: Sequence[Sequence[Fraction]],
    l: Sequence[Sequence[Fraction]],
) -> Mapping[str, Any]:
    target = matrix_vector_mul(l, factor.vector)
    reconstructed_source = matrix_vector_mul(c, target)
    if reconstructed_source != factor.vector:
        raise AdapterFormatError(
            "dual residual factor vector is not in the centered subspace generated by x0-x_star, g0, g1"
        )
    return {
        "weight": factor.weight_source,
        "vector": decimal_vector_json(target),
    }


def adapt_source(source: SourceArtifact) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    mismatches, expected_fp, computed_fp = compare_source(source)
    c, l = build_basis_maps(source)

    target_gram = matrix_mul(matrix_mul(transpose(c), source.primal_gram), c)
    target_dual = matrix_mul(matrix_mul(l, source.dual_residual), transpose(l))
    reconstructed_residual = matrix_mul(matrix_mul(c, target_dual), transpose(c))
    if reconstructed_residual != source.dual_residual:
        mismatches.append(
            mismatch(
                "solver_output.dual_residual.centered_reconstruction",
                rational_matrix_json(source.dual_residual),
                rational_matrix_json(reconstructed_residual),
            )
        )

    point_index = {label: k for k, label in enumerate(source.point_order)}
    if set(point_index) != set(EXPECTED_POINT_ORDER):
        fail(
            "$.problem.point_order",
            "adapter requires exactly star, x0, x1 labels even when their order is being audited",
        )
    star_source = source.point_decomposition[point_index["star"]]
    target_positions: list[tuple[Fraction, ...]] = []
    target_gradients: list[tuple[Fraction, ...]] = []
    for label in TARGET_POINT_ORDER:
        source_position = source.point_decomposition[point_index[label]]
        centered = vector_sub(source_position, star_source)
        coords = matrix_vector_mul(l, centered)
        if matrix_vector_mul(c, coords) != centered:
            mismatches.append(
                mismatch(
                    f"translation.position[{label}]",
                    rational_vector_json(centered),
                    rational_vector_json(matrix_vector_mul(c, coords)),
                )
            )
        target_positions.append(coords)
        source_gradient = source.gradient_decomposition[point_index[label]]
        grad_coords = matrix_vector_mul(l, source_gradient)
        if matrix_vector_mul(c, grad_coords) != source_gradient:
            mismatches.append(
                mismatch(
                    f"translation.gradient[{label}]",
                    rational_vector_json(source_gradient),
                    rational_vector_json(matrix_vector_mul(c, grad_coords)),
                )
            )
        target_gradients.append(grad_coords)

    initial_constraints = [cst for cst in source.constraints if cst.kind == "initial"]
    if len(initial_constraints) != 1:
        fail("$.problem.constraints", f"expected exactly one initial constraint, got {len(initial_constraints)}")
    assumption_source = initial_constraints[0].expr.neg()
    target_assumption = transform_expr_to_target(assumption_source, source, l)
    lifted_assumption_gram = matrix_mul(
        matrix_mul(c, target_assumption.gram_coeff), transpose(c)
    )
    if lifted_assumption_gram != assumption_source.gram_coeff:
        mismatches.append(
            mismatch(
                "translation.initial_assumption.gram",
                rational_matrix_json(assumption_source.gram_coeff),
                rational_matrix_json(lifted_assumption_gram),
            )
        )

    target_objective = transform_expr_to_target(source.objective, source, l)
    lifted_objective_gram = matrix_mul(
        matrix_mul(c, target_objective.gram_coeff), transpose(c)
    )
    if lifted_objective_gram != source.objective.gram_coeff:
        mismatches.append(
            mismatch(
                "translation.objective.gram",
                rational_matrix_json(source.objective.gram_coeff),
                rational_matrix_json(lifted_objective_gram),
            )
        )

    value_index = {label: k for k, label in enumerate(source.value_order)}
    target_values = tuple(source.function_values[value_index[label]] for label in EXPECTED_VALUE_ORDER)
    target_value_sources = tuple(
        source.function_value_sources[value_index[label]] for label in EXPECTED_VALUE_ORDER
    )

    interp_terms: list[Mapping[str, Any]] = []
    assumption_terms: list[Mapping[str, Any]] = []
    for constraint in source.constraints:
        # Zero dual multipliers carry no mathematical information.  The full
        # source constraint ordering is audited separately, while the adapted
        # exact upper certificate keeps only nonzero terms.
        if constraint.dual == 0:
            continue
        if constraint.kind == "initial":
            assumption_terms.append({"weight": constraint.dual_source, "index": 0})
        else:
            assert constraint.i is not None and constraint.j is not None
            source_i_label = source.point_order[constraint.i]
            source_j_label = source.point_order[constraint.j]
            target_i = TARGET_POINT_ORDER.index(source_i_label)
            target_j = TARGET_POINT_ORDER.index(source_j_label)
            interp_terms.append(
                {"weight": constraint.dual_source, "i": target_i, "j": target_j}
            )

    # Canonicalize the mathematical certificate independently of PEPit's source
    # constraint order.  The source order is audited above as provenance and
    # formulation metadata; the downstream exact Gram bundle uses a stable
    # typed ordering so that a source-order mismatch cannot perturb its
    # numerical semantics.
    interp_terms.sort(key=lambda term: (term["i"], term["j"]))
    assumption_terms.sort(key=lambda term: term["index"])

    approximate = {
        "schema_version": 1,
        "source": (
            "PEPit one-step GD solver artifact adapted from "
            f"commit {source.producer['git_commit']} (source sha256 {source.source_sha256})"
        ),
        "declared": {
            "point_count": 3,
            "gram_basis_count": 3,
            "ordered_pair_count": 9,
            "assumption_count": 1,
            "primal_factor_count": len(source.primal_factors),
            "upper_interp_term_count": len(interp_terms),
            "upper_assumption_term_count": len(assumption_terms),
            "dual_factor_count": len(source.dual_factors),
        },
        "ordering": {
            "points": list(TARGET_POINT_ORDER),
            "gram_basis": list(TARGET_GRAM_BASIS),
        },
        "policy": dict(source.policy),
        "expect": {
            "raw": source.expect_raw,
            "reconstructed": source.expect_reconstructed,
        },
        "model": {
            "position": [decimal_vector_json(row) for row in target_positions],
            "gradient": [decimal_vector_json(row) for row in target_gradients],
            "assumptions": [
                {
                    "name": "initial_radius",
                    "expr": {
                        "const": decimal_string(target_assumption.const),
                        "value_coeff": decimal_vector_json(target_assumption.value_coeff),
                        "gram_coeff": decimal_matrix_json(target_assumption.gram_coeff),
                    },
                }
            ],
        },
        "primal": {
            "gram": decimal_matrix_json(target_gram),
            "value": list(target_value_sources),
            "gram_factor": {
                "factors": [
                    transform_factor_primal(factor, c)
                    for factor in source.primal_factors
                ]
            },
        },
        "upper": {
            "bound": source.dual_objective_source,
            "objective": {
                "const": decimal_string(target_objective.const),
                "value_coeff": decimal_vector_json(target_objective.value_coeff),
                "gram_coeff": decimal_matrix_json(target_objective.gram_coeff),
            },
            "interp_terms": interp_terms,
            "assumption_terms": assumption_terms,
            "dual_matrix": decimal_matrix_json(target_dual),
            "dual_factor": {
                "factors": [
                    transform_factor_dual(factor, c, l)
                    for factor in source.dual_factors
                ]
            },
        },
    }

    approximate_sha256 = base.canonical_json_sha256(approximate)
    report = {
        "schema_version": ADAPTER_REPORT_VERSION,
        "adapter_id": ADAPTER_ID,
        "adapter_generator_version": ADAPTER_GENERATOR_VERSION,
        "source_artifact_sha256": source.source_sha256,
        "adapted_approximate_gram_sha256": approximate_sha256,
        "accepted": not mismatches,
        "expected_model_fingerprint": expected_fp,
        "declared_model_fingerprint": source.declared_model_fingerprint,
        "computed_model_fingerprint": computed_fp,
        "producer": dict(source.producer),
        "capture_mode": source.capture_mode,
        "live_solver_claim": source.capture_mode == "live_pepit",
        "source_ordering": {
            "points": list(source.point_order),
            "function_values": list(source.value_order),
            "leaf_points": list(source.leaf_order),
            "constraints": list(source.constraint_order),
        },
        "expected_ordering": {
            "points": list(EXPECTED_POINT_ORDER),
            "function_values": list(EXPECTED_VALUE_ORDER),
            "leaf_points": list(EXPECTED_LEAF_ORDER),
            "constraints": list(EXPECTED_CONSTRAINT_ORDER),
        },
        "mismatches": mismatches,
        "solver_values": {
            "primal_objective": source.primal_objective_source,
            "dual_objective": source.dual_objective_source,
        },
        "factorization_hint_checks": {
            "primal_exact_for_source_matrix":
                factor_matrix(source.primal_factors) == source.primal_gram,
            "dual_exact_for_source_matrix":
                factor_matrix(source.dual_factors) == source.dual_residual,
            "note": (
                "factor hints are untrusted numerical postprocessing; exact "
                "acceptance is decided only by downstream Gram audits"
            ),
        },
        "target": {
            "point_order": list(TARGET_POINT_ORDER),
            "gram_basis_order": list(TARGET_GRAM_BASIS),
            "centered_primal_gram": decimal_matrix_json(target_gram),
            "centered_dual_matrix": decimal_matrix_json(target_dual),
        },
    }
    return approximate, report


def build_manifest(
    source: SourceArtifact, report: Mapping[str, Any]
) -> Mapping[str, Any]:
    """Build the canonical adapter-stage provenance manifest."""

    return {
        "schema_version": 1,
        "kind": "lean-pep-pepit-one-step-adapter-manifest-v1",
        "adapter_id": ADAPTER_ID,
        "adapter_generator_version": ADAPTER_GENERATOR_VERSION,
        "hashes": {
            "source_artifact_sha256": source.source_sha256,
            "adapted_approximate_gram_sha256": report["adapted_approximate_gram_sha256"],
            "adapter_report_sha256": base.canonical_json_sha256(report),
        },
        "producer": dict(source.producer),
        "semantics": {
            "source_formulation": "audited separately from the numerical Gram tracks",
            "numerical_payload": "sent through approximate-gram-format-v1 and both exact Gram audits",
        },
    }


def lean_string(value: str) -> str:
    return base.lean_string(value)


def lean_string_list(values: Sequence[str]) -> str:
    return "[" + ", ".join(lean_string(value) for value in values) + "]"


def lean_rat(value: Fraction) -> str:
    return base.lean_rat(value)


def lean_vector(values: Sequence[Fraction]) -> str:
    return exact.lean_vector(values)


def lean_matrix(values: Sequence[Sequence[Fraction]]) -> str:
    return exact.lean_matrix(values)


def render_source_linear_expr(expr: LinearExpr, indent: str) -> list[str]:
    return [
        indent + "{ constCoeff := " + lean_rat(expr.const),
        indent + "  valueCoeff := " + lean_vector(expr.value_coeff),
        indent + "  gramCoeff := " + lean_matrix(expr.gram_coeff) + " }",
    ]


def render_source_constraint(constraint: ConstraintSpec, indent: str) -> list[str]:
    kind = ".initial" if constraint.kind == "initial" else ".interpolation"
    sense = ".le"
    i = "none" if constraint.i is None else f"some {constraint.i}"
    j = "none" if constraint.j is None else f"some {constraint.j}"
    # Keep the nested `LinearExprQ` record on its own layout block.  Writing
    # `expr := { constCoeff := ...` inline and then indenting later fields only
    # relative to the outer record makes Lean's layout parser close the inner
    # record after `constCoeff`.
    expr_lines = render_source_linear_expr(constraint.expr, indent + "    ")
    return [
        indent + "{ label := " + lean_string(constraint.label),
        indent + "  kind := " + kind,
        indent + "  sense := " + sense,
        indent + "  i := " + i,
        indent + "  j := " + j,
        indent + "  expr :=",
        *expr_lines[:-1],
        expr_lines[-1] + " }",
    ]


def render_source_constraints(constraints: Sequence[ConstraintSpec], indent: str) -> list[str]:
    lines = [indent + "!["]
    for index, constraint in enumerate(constraints):
        rendered = render_source_constraint(constraint, indent + "  ")
        if index + 1 < len(constraints):
            rendered[-1] += ","
        lines.extend(rendered)
    lines.append(indent + "]")
    return lines


def render_adapter_lean(
    source: SourceArtifact,
    report: Mapping[str, Any],
    manifest: Mapping[str, Any],
    namespace: str,
    *,
    comparison_import: str | None,
) -> str:
    ns_parts = base.validate_namespace(namespace)
    c, _ = build_basis_maps(source)
    native_to_centered = transpose(c)
    imports = ["import LeanPEP.Adapters.PEPitOneStep"]
    if comparison_import:
        imports.append(f"import {comparison_import}")
    lines: list[str] = [
        *imports,
        "",
        "/-!",
        "Generated by `tools/adapt_pepit_one_step.py`.",
        "The adapter is untrusted; Lean compares the generated source metadata",
        "against the pinned one-step PEPit formulation, while all mathematical",
        "bundles are independently checked by the existing Gram auditor.",
        "",
        f"Source artifact SHA-256: {source.source_sha256}",
        f"Adapter generator version: {ADAPTER_GENERATOR_VERSION}",
        "-/",
        "",
        *base.render_namespace_open(ns_parts),
        "",
        "def symbolicSourceQ : LeanPEP.Adapters.PEPitOneStep.SymbolicSourceQ :=",
        "  { pointDecomposition := " + lean_matrix(source.point_decomposition),
        "    gradientDecomposition := " + lean_matrix(source.gradient_decomposition),
        "    constraints :=",
        *render_source_constraints(source.constraints, "      "),
        "    objective :=",
        *render_source_linear_expr(source.objective, "      "),
        "    nativeToCentered := " + lean_matrix(native_to_centered) + " }",
        "",
        "def sourceQ : LeanPEP.Adapters.PEPitOneStep.SourceQ :=",
        f"  {{ producerName := {lean_string(source.producer['name'])}",
        f"    producerCommit := {lean_string(source.producer['git_commit'])}",
        f"    packageVersion := {lean_string(source.producer['package_version'])}",
        f"    wrapperName := {lean_string(source.producer['wrapper'])}",
        f"    solverName := {lean_string(source.producer['solver'])}",
        f"    solverStatus := {lean_string(source.producer['solver_status'])}",
        f"    captureMode := {lean_string(source.capture_mode)}",
        f"    adapterId := {lean_string(source.adapter_id)}",
        f"    functionClass := {lean_string(source.function_class)}",
        f"    smoothness := {lean_string(source.smoothness_source)}",
        f"    stepSize := {lean_string(source.step_size_source)}",
        f"    steps := {source.steps}",
        f"    pointOrder := {lean_string_list(source.point_order)}",
        f"    functionValueOrder := {lean_string_list(source.value_order)}",
        f"    leafPointOrder := {lean_string_list(source.leaf_order)}",
        f"    constraintOrder := {lean_string_list(source.constraint_order)}",
        f"    modelFingerprint := {lean_string(source.declared_model_fingerprint)}",
        "    symbolic := symbolicSourceQ",
        f"    sourceSha256 := {lean_string(source.source_sha256)}",
        f"    adaptedApproxSha256 := {lean_string(report['adapted_approximate_gram_sha256'])}",
        f"    adapterReportSha256 := {lean_string(base.canonical_json_sha256(report))}",
        f"    adapterManifestSha256 := {lean_string(base.canonical_json_sha256(manifest))}",
        f"    adapterGeneratorVersion := {lean_string(ADAPTER_GENERATOR_VERSION)} }}",
        "",
        "def auditQ : LeanPEP.Adapters.PEPitOneStep.AuditReportQ :=",
        "  LeanPEP.Adapters.PEPitOneStep.auditSourceQ sourceQ",
        "",
    ]
    if comparison_import:
        lines.extend(
            [
                "def comparisonQ : LeanPEP.Adapters.PEPitOneStep.AdapterAuditReportQ :=",
                "  LeanPEP.Adapters.PEPitOneStep.auditAdapterOptionalQ",
                f"    sourceQ (some {comparison_import}.comparisonQ)",
                "",
            ]
        )
    if source.expect_adapter == "accepted":
        lines.extend(
            [
                "theorem sourceQ_check :",
                "    LeanPEP.Adapters.PEPitOneStep.checkSourceQ sourceQ = true := by",
                "  native_decide",
                "",
            ]
        )
    elif source.expect_adapter == "rejected":
        lines.extend(
            [
                "theorem sourceQ_rejected :",
                "    LeanPEP.Adapters.PEPitOneStep.checkSourceQ sourceQ = false := by",
                "  native_decide",
                "",
            ]
        )
    if comparison_import and source.expect_adapter == "accepted" and source.expect_reconstructed == "accepted":
        lines.extend(
            [
                "theorem comparisonQ_accepted : comparisonQ.accepted = true := by",
                "  native_decide",
                "",
            ]
        )
    elif comparison_import and source.expect_adapter == "rejected":
        lines.extend(
            [
                "theorem comparisonQ_rejected : comparisonQ.accepted = false := by",
                "  native_decide",
                "",
            ]
        )
    # Keep Python report acceptance visible without using it as Lean's criterion.
    lines.extend(
        [
            f"def pythonAdapterAccepted : Bool := {str(bool(report['accepted'])).lower()}",
            "",
            *base.render_namespace_close(ns_parts),
            "",
        ]
    )
    return "\n".join(lines)


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
    fd, temp_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
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


def load_json(path: Path) -> Mapping[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle, object_pairs_hook=exact.reject_duplicate_pairs)
    except OSError as exc:
        raise AdapterFormatError(f"cannot read {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise AdapterFormatError(
            f"invalid JSON at line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc
    except exact.ImportFormatError as exc:
        raise AdapterFormatError(str(exc)) from exc


def write_or_check(path: Path, content: str, *, check: bool) -> None:
    if check:
        try:
            existing = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise AdapterFormatError(f"cannot read generated output {path}: {exc}") from exc
        if existing != content:
            raise AdapterFormatError(f"generated output is stale: {path}; regenerate it")
    else:
        atomic_write(path, content)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="pepit-sdp-artifact-v1 JSON input")
    parser.add_argument("--approximate-gram", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--lean-metadata", required=True, type=Path)
    parser.add_argument("--lean-namespace", required=True)
    parser.add_argument(
        "--comparison-import",
        help="optional generated raw/reconstructed comparison module imported by the metadata module",
    )
    parser.add_argument("--check", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        source = parse_source(load_json(args.input))
        approximate, report = adapt_source(source)
        manifest = build_manifest(source, report)
        lean = render_adapter_lean(
            source,
            report,
            manifest,
            args.lean_namespace,
            comparison_import=args.comparison_import,
        )
        write_or_check(
            args.approximate_gram, render_json(approximate), check=args.check
        )
        write_or_check(args.report, render_json(report), check=args.check)
        write_or_check(args.manifest, render_json(manifest), check=args.check)
        write_or_check(args.lean_metadata, lean, check=args.check)
        if source.expect_adapter == "accepted" and not report["accepted"]:
            raise AdapterFormatError(
                "fixture expected adapter acceptance but formulation mismatches were reported"
            )
        if source.expect_adapter == "rejected" and report["accepted"]:
            raise AdapterFormatError(
                "fixture expected adapter rejection but no formulation mismatch was reported"
            )
        return 0
    except (AdapterFormatError, exact.ImportFormatError, base.ImportFormatError) as exc:
        print(f"adapt_pepit_one_step.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
