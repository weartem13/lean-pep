#!/usr/bin/env python3
"""D2 deterministic regression fixtures, not solver captures.

The independent target matrix is target minus the weighted constraints. D1
synthesizes factors of that exact matrix. The imported source remains a literal
snapshot; the expected model is reconstructed only by Lean's old C2 compiler.
"""
from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as src
import synthesize_psd_factors as psd

ROOT = Path(__file__).resolve().parents[1]


def fixture(T: int) -> dict:
    s = src.expected_snapshot(T)
    p, m = src.dimensions(T)
    nf, nh = T+2, T+1
    terms: list[tuple[int, Q]] = []
    for i in range(T+1):
        w = Q(1, 2*T) if i == 0 else Q(1, T+1) if i == T else Q(2*T+1, (2*T-i)*(2*T-i+1))
        terms.append((i+1, w))
    terms += [((i+1)*nf+i+2, Q(i+1, 2*T-i)) for i in range(T)]
    terms += [(nf*nf+j+1, Q(2*T, (2*T-j-1)*(2*T-j))) for j in range(T)]
    terms += [(nf*nf+(j+1)*nh+j+2, Q(j+1, 2*T-j-1)) for j in range(T-1)]
    bound = Q(1, 4*T)
    terms.append((nf*nf+nh*nh, bound))
    target = src.add(gram.LinearExprSpec(bound, (Q(0),)*p, src.zero(p,m).gram_coeff), src.scale(Q(-1), s.objective))
    residual = target
    for i, w in terms:
        residual = src.add(residual, src.scale(-w, s.constraints[i]))
    if residual.const != 0 or any(residual.value_coeff):
        raise ArithmeticError('Fixture weights failed scalar cancellation')
    matrix = residual.gram_coeff  # target matrix defined BEFORE factor synthesis
    factors = psd.synthesize_psd(matrix)
    if factors.status != 'psd' or not psd.verify_result(matrix, factors):
        raise ArithmeticError('Fixture matrix did not have an exact PSD decomposition')
    raw = dict(format=src.FORMAT, horizon=T,
        origin=dict(mode='deterministic_regression_fixture',
            description=f'D2 centered {T}-step PG exact regression; closed-form weights, no solver call'),
        source=src.source_tree(s),
        upper=dict(bound=bound, objective=src.source_tree(s)['objective'], interp_terms=[],
            assumption_terms=[dict(index=i, weight=w) for i,w in terms],
            dual_matrix=matrix,
            dual_factor=dict(factors=[dict(weight=t.weight, vector=t.vector) for t in factors.factors])))
    return src.exact_json(raw)


def build_fixtures() -> None:
    """Explicit fixture creation mode; normal regeneration only READS inputs."""
    for T, name in ((1,'one'), (2,'two'), (3,'three')):
        path = ROOT/f'data/fixtures/composite_source/pg_{name}_step.json'
        gram.atomic_write(path, json.dumps(fixture(T), indent=2, sort_keys=True)+'\n')
        print(path.relative_to(ROOT))


def generate() -> dict[Path, str]:
    blocks = ['import LeanPEP.Adapters.ProximalGradientSource\n']
    reports = []
    for T, name, ns in ((1,'one','PGOne'), (2,'two','PGTwo'), (3,'three','PGThree')):
        raw = gram.load_json(ROOT/f'data/fixtures/composite_source/pg_{name}_step.json')
        a = src.parse_artifact(raw, expected_steps=T)
        blocks.append(src.render_module(a, 'LeanPEP.Imported.CompositeSource.'+ns).split('\n',1)[1])
        reports.append(src.diagnose(a))
    return {
        ROOT/'LeanPEP/Imported/CompositeSource.lean': '\n'.join(blocks),
        ROOT/'data/fixtures/composite_source_generated/diagnostics.json': json.dumps(reports, indent=2, sort_keys=True)+'\n',
    }


def main() -> None:
    if sys.argv[1:] == ['--create-fixtures']:
        build_fixtures()
    elif sys.argv[1:]:
        raise SystemExit('Only optional argument: --create-fixtures')
    for path, text in generate().items():
        gram.atomic_write(path, text)
        print(path.relative_to(ROOT))


if __name__ == '__main__':
    main()
