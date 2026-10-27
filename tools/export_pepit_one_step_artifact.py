#!/usr/bin/env python3
"""Export one live PEPit one-step GD solve as `pepit-sdp-artifact-v1`.

The live PEPit exporter is intentionally version-pinned and narrow.  It reads PEPit's
actual leaf-point/function-value order, prepared scalar constraints, primal
Gram/function values, scalar dual multipliers, and dual residual matrix after a
solve.  The resulting JSON remains untrusted and must be passed through
`adapt_pepit_one_step.py` and the existing Lean Gram auditors.

PEPit and NumPy are imported lazily, so `--help` and static tests work even when
the optional solver environment is not installed.
"""

from __future__ import annotations

import argparse
import importlib.metadata
import json
import math
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import adapt_pepit_one_step as adapter


def finite_float_string(value: Any, path: str) -> str:
    number = float(value)
    if not math.isfinite(number):
        raise ValueError(f"{path}: expected a finite solver number, got {number!r}")
    # Python's repr is the shortest round-trip decimal for the binary float.
    return repr(number)


def zero_matrix(n: int) -> list[list[float]]:
    return [[0.0 for _ in range(n)] for _ in range(n)]


def expression_coefficients(expr: Any, leaf_points: Sequence[Any], leaf_values: Sequence[Any]) -> dict[str, Any]:
    """Translate a PEPit Expression decomposition into source-order coefficients."""

    from PEPit.expression import Expression
    from PEPit.point import Point
    from PEPit.tools.dict_operations import prune_dict, symmetrize_dict

    point_index = {point: i for i, point in enumerate(leaf_points)}
    value_index = {value: i for i, value in enumerate(leaf_values)}
    p = len(leaf_values)
    n = len(leaf_points)
    const = 0.0
    value_coeff = [0.0 for _ in range(p)]
    gram_coeff = zero_matrix(n)
    decomposition = prune_dict(symmetrize_dict(expr.decomposition_dict))
    for key, coeff in decomposition.items():
        coefficient = float(coeff)
        if key == 1:
            const += coefficient
        elif isinstance(key, Expression):
            if key not in value_index:
                raise ValueError("expression references an unknown leaf function value")
            value_coeff[value_index[key]] += coefficient
        elif isinstance(key, tuple) and len(key) == 2 and all(isinstance(x, Point) for x in key):
            left, right = key
            if left not in point_index or right not in point_index:
                raise ValueError("expression references an unknown leaf point")
            gram_coeff[point_index[left]][point_index[right]] += coefficient
        else:
            raise TypeError(f"unsupported PEPit expression key {key!r}")
    return {
        "const": finite_float_string(const, "expression.const"),
        "value_coeff": [finite_float_string(x, "expression.value_coeff") for x in value_coeff],
        "gram_coeff": [
            [finite_float_string(x, "expression.gram_coeff") for x in row]
            for row in gram_coeff
        ],
    }


def point_coefficients(point: Any, leaf_points: Sequence[Any]) -> list[str]:
    index = {leaf: i for i, leaf in enumerate(leaf_points)}
    coeff = [0.0 for _ in leaf_points]
    for leaf, value in point.decomposition_dict.items():
        if leaf not in index:
            raise ValueError("point decomposition references an unknown leaf point")
        coeff[index[leaf]] += float(value)
    return [finite_float_string(x, "point decomposition") for x in coeff]


def factor_hints_from_centered_matrices(G: Any, residual: Any, *, tolerance: float) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Produce untrusted numerical factor hints in the PEPit leaf basis.

    The factors are obtained after projecting to the canonical centered basis
    `[x0-x_star, g0, g1]`.  They are hints only; the downstream exact Gram
    checker decides whether either exact track accepts them.
    """

    import numpy as np

    C = np.array(
        [
            [-1.0, 0.0, 0.0],
            [1.0, 0.0, 0.0],
            [0.0, 1.0, 0.0],
            [0.0, 0.0, 1.0],
        ]
    )
    L = np.array(
        [
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
        ]
    )

    centered_primal = C.T @ np.asarray(G, dtype=float) @ C
    centered_dual = L @ np.asarray(residual, dtype=float) @ L.T

    def eig_factors(matrix: Any, lift: Any, label: str) -> list[dict[str, Any]]:
        matrix = (matrix + matrix.T) / 2
        values, vectors = np.linalg.eigh(matrix)
        factors: list[dict[str, Any]] = []
        for k, value in enumerate(values):
            if abs(float(value)) <= tolerance:
                continue
            source_vector = lift @ vectors[:, k]
            factors.append(
                {
                    "weight": finite_float_string(value, f"{label}.eigenvalue[{k}]"),
                    "vector": [
                        finite_float_string(x, f"{label}.eigenvector[{k}]")
                        for x in source_vector
                    ],
                }
            )
        return factors

    # For primal hints C^T (L^T v) = v.  For dual hints, C v lies exactly in
    # the centered source subspace required by the adapter.
    return (
        eig_factors(centered_primal, L.T, "primal"),
        eig_factors(centered_dual, C, "dual"),
    )


def build_artifact(args: argparse.Namespace) -> Mapping[str, Any]:
    try:
        import numpy as np
        from PEPit import PEP
        from PEPit.expression import Expression
        from PEPit.functions import SmoothConvexFunction
        from PEPit.point import Point
    except ImportError as exc:
        raise RuntimeError(
            "PEPit, NumPy, and a configured PEPit solver wrapper are required to export a live artifact"
        ) from exc

    problem = PEP()
    function = problem.declare_function(SmoothConvexFunction, L=1.0)
    function.set_name("f")
    x_star, g_star, f_star = function.stationary_point(
        return_gradient_and_function_value=True, name="x_star"
    )
    g_star.set_name("g_star")
    f_star.set_name("f_star")

    x0 = problem.set_initial_point(name="x0")
    initial = (x0 - x_star) ** 2 <= 1.0
    problem.set_initial_condition(initial, name="initial_radius")

    g0 = function.gradient(x0, name="g0")
    f0 = function.value(x0, name="f0")
    x1 = x0 - g0
    x1.set_name("x1")
    g1 = function.gradient(x1, name="g1")
    f1 = function.value(x1, name="f1")
    metric = f1 - f_star
    metric.set_name("f1_minus_f_star")
    problem.set_performance_metric(metric)

    dual_objective = problem.solve(
        wrapper=args.wrapper,
        solver=args.solver,
        verbose=args.verbose,
    )
    if dual_objective is None:
        raise RuntimeError("PEPit returned no finite objective")

    leaf_points = tuple(Point.list_of_leaf_points)
    # `PEP.solve` creates one additional leaf expression for the max-min
    # objective tau.  The adapter's sampled function-value order is the three
    # explicit function values, not the global Expression list after solve.
    leaf_values = (f_star, f0, f1)
    expected_point_objects = (x_star, x0, x1)
    expected_gradient_objects = (g_star, g0, g1)
    if len(leaf_points) != 4:
        raise RuntimeError(f"expected four PEPit leaf points, got {len(leaf_points)}")

    actual_leaf_names = [point.get_name() for point in leaf_points]
    if actual_leaf_names != list(adapter.EXPECTED_LEAF_ORDER):
        raise RuntimeError(
            f"unexpected PEPit leaf order: expected {list(adapter.EXPECTED_LEAF_ORDER)}, got {actual_leaf_names}"
        )
    actual_value_names = [value.get_name() for value in leaf_values]
    if actual_value_names != list(adapter.EXPECTED_VALUE_ORDER):
        raise RuntimeError(
            f"unexpected PEPit sampled-value order: expected {list(adapter.EXPECTED_VALUE_ORDER)}, got {actual_value_names}"
        )

    prepared_constraints = tuple(problem._list_of_constraints_sent_to_wrapper)
    if len(prepared_constraints) != 8:
        raise RuntimeError(
            f"expected one performance constraint plus seven formulation constraints, got {len(prepared_constraints)}"
        )
    performance_constraint = prepared_constraints[0]
    if performance_constraint.get_name() != "Performance metric 1":
        raise RuntimeError(
            f"unexpected PEPit performance constraint name {performance_constraint.get_name()!r}"
        )
    performance_dual = float(performance_constraint.eval_dual())
    if not math.isclose(performance_dual, 1.0, rel_tol=1e-7, abs_tol=1e-7):
        raise RuntimeError(
            f"single performance metric dual should be numerically one, got {performance_dual!r}"
        )
    constraints = prepared_constraints[1:]
    expected_pepit_names = [
        "initial_radius",
        "IC_f_smoothness_convexity(x_star, x0)",
        "IC_f_smoothness_convexity(x_star, x1)",
        "IC_f_smoothness_convexity(x0, x_star)",
        "IC_f_smoothness_convexity(x0, x1)",
        "IC_f_smoothness_convexity(x1, x_star)",
        "IC_f_smoothness_convexity(x1, x0)",
    ]
    actual_constraint_names = [constraint.get_name() for constraint in constraints]
    if actual_constraint_names != expected_pepit_names:
        raise RuntimeError(
            "unexpected PEPit prepared constraint ordering:\n"
            f"expected {expected_pepit_names}\nactual   {actual_constraint_names}"
        )

    pairs: list[tuple[int, int] | None] = [None, (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]
    constraint_records: list[dict[str, Any]] = []
    for index, (constraint, label, pair) in enumerate(
        zip(constraints, adapter.EXPECTED_CONSTRAINT_ORDER, pairs, strict=True)
    ):
        record: dict[str, Any] = {
            "label": label,
            "kind": "initial" if pair is None else "interpolation",
            "sense": "le",
            "expr": expression_coefficients(constraint.expression, leaf_points, leaf_values),
            "dual": finite_float_string(constraint.eval_dual(), f"constraint[{index}].dual"),
        }
        if pair is not None:
            record["i"], record["j"] = pair
        constraint_records.append(record)

    point_decomposition = [point_coefficients(point, leaf_points) for point in expected_point_objects]
    gradient_decomposition = [
        point_coefficients(gradient, leaf_points) for gradient in expected_gradient_objects
    ]
    objective = expression_coefficients(metric, leaf_points, leaf_values)

    G = np.asarray(problem.G_value, dtype=float)
    residual = np.asarray(problem.residual, dtype=float)
    if G.shape != (4, 4) or residual.shape != (4, 4):
        raise RuntimeError(
            f"unexpected PEPit matrix shapes: G={G.shape}, residual={residual.shape}"
        )
    primal_factors, dual_factors = factor_hints_from_centered_matrices(
        G, residual, tolerance=args.factor_tolerance
    )

    problem_payload = {
        "adapter_id": adapter.ADAPTER_ID,
        "function_class": adapter.PEPIT_FUNCTION_CLASS,
        "smoothness": "1",
        "step_size": "1",
        "steps": 1,
        "point_order": list(adapter.EXPECTED_POINT_ORDER),
        "function_value_order": list(adapter.EXPECTED_VALUE_ORDER),
        "leaf_point_order": list(adapter.EXPECTED_LEAF_ORDER),
        "point_decomposition": point_decomposition,
        "gradient_decomposition": gradient_decomposition,
        "constraints": constraint_records,
        "objective": objective,
    }

    # Parse our own source-independent formulation payload using the adapter's
    # exact decimal grammar, then compute the canonical model fingerprint.
    temporary = {
        "schema_version": 1,
        "producer": {
            "name": "PEPit",
            "package_version": "temporary",
            "git_commit": args.pepit_commit,
            "wrapper": args.wrapper,
            "solver": args.solver or "default",
            "solver_status": "temporary",
            "capture_mode": "live_pepit",
        },
        "problem": {**problem_payload, "model_fingerprint": "temporary"},
        "solver_output": {
            "primal_gram": [["0"] * 4 for _ in range(4)],
            "function_values": ["0"] * 3,
            "dual_residual": [["0"] * 4 for _ in range(4)],
            "primal_objective": "0",
            "dual_objective": "0",
        },
        "factorization_hints": {
            "primal_gram": {"factors": []},
            "dual_residual": {"factors": []},
        },
        "reconstruction_policy": {
            "method": "limit_denominator",
            "max_denominator": args.max_denominator,
            "max_abs_error": args.max_abs_error,
        },
    }
    parsed_temporary = adapter.parse_source(temporary)
    fingerprint = adapter.source_model_fingerprint(parsed_temporary)
    problem_payload["model_fingerprint"] = fingerprint

    try:
        package_version = importlib.metadata.version("PEPit")
    except importlib.metadata.PackageNotFoundError:
        package_version = "unknown"
    solver_status = "unknown"
    cvxpy_problem = getattr(getattr(problem, "wrapper", None), "prob", None)
    if cvxpy_problem is not None and getattr(cvxpy_problem, "status", None) is not None:
        solver_status = str(cvxpy_problem.status)

    artifact = {
        "schema_version": 1,
        "producer": {
            "name": "PEPit",
            "package_version": package_version,
            "git_commit": args.pepit_commit,
            "wrapper": str(problem.wrapper_name or args.wrapper),
            "solver": str(args.solver or "wrapper-default"),
            "solver_status": solver_status,
            "capture_mode": "live_pepit",
        },
        "problem": problem_payload,
        "solver_output": {
            "primal_gram": [
                [finite_float_string(x, "G") for x in row] for row in G
            ],
            "function_values": [
                finite_float_string(value.eval(), "sampled function value")
                for value in leaf_values
            ],
            "dual_residual": [
                [finite_float_string(x, "residual") for x in row]
                for row in residual
            ],
            "primal_objective": finite_float_string(
                problem.objective.eval(), "primal objective"
            ),
            "dual_objective": finite_float_string(dual_objective, "dual objective"),
        },
        "factorization_hints": {
            "source": (
                "untrusted numerical eigendecomposition after projection to the "
                "canonical centered basis; not native PEPit proof output"
            ),
            "primal_gram": {
                "method": "centered_eigh",
                "factors": primal_factors,
            },
            "dual_residual": {
                "method": "centered_eigh",
                "factors": dual_factors,
            },
        },
        "reconstruction_policy": {
            "method": "limit_denominator",
            "max_denominator": args.max_denominator,
            "max_abs_error": args.max_abs_error,
        },
        "expect": {
            "adapter": "accepted",
            "raw": "unchecked",
            "reconstructed": "unchecked",
        },
    }
    return artifact


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="output pepit-sdp-artifact-v1 JSON")
    parser.add_argument("--wrapper", default="cvxpy")
    parser.add_argument("--solver", default="CLARABEL")
    parser.add_argument("--verbose", type=int, default=1)
    parser.add_argument(
        "--pepit-commit",
        default=adapter.PEPIT_COMMIT,
        help="PEPit Git commit whose internals/order are being asserted",
    )
    parser.add_argument("--factor-tolerance", type=float, default=1e-12)
    parser.add_argument("--max-denominator", type=int, default=1000000)
    parser.add_argument("--max-abs-error", default="1e-8")
    parser.add_argument("--check", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.pepit_commit != adapter.PEPIT_COMMIT:
            raise ValueError(
                f"this adapter is pinned to PEPit commit {adapter.PEPIT_COMMIT}; got {args.pepit_commit}"
            )
        artifact = build_artifact(args)
        content = json.dumps(
            artifact,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
            separators=(",", ": "),
        ) + "\n"
        if args.check:
            existing = args.output.read_text(encoding="utf-8")
            if existing != content:
                raise ValueError(f"exported artifact is stale: {args.output}")
        else:
            adapter.atomic_write(args.output, content)
        return 0
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        print(f"export_pepit_one_step_artifact.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
