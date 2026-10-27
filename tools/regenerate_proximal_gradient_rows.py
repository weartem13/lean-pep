#!/usr/bin/env python3
"""D5 exact regression inputs, NOT live solver captures.

Explicit --create-fixtures creates row-scaled candidates from existing D4 inputs.
Normal regeneration ONLY reads the committed candidates, never the expected model.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_ordering as order
import import_proximal_gradient_rows as rows

ROOT = Path(__file__).resolve().parents[1]
CASES = ((1,'one','PGOne'), (2,'two','PGTwo'), (3,'three','PGThree'), (1,'unit','PGUnit'))


def fixture(T: int, unit: bool=False) -> dict:
    word = 'identity' if unit else {1:'one',2:'two',3:'three'}[T]
    a = order.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_ordering/pg_{word}.json'),T)
    scales = (Q(2),Q(1,3),Q(5,2),Q(7),Q(4,5))
    rs = tuple(rows.Rule('geZero' if unit or i % 2 == 0 else 'leZero',
        Q(1) if unit else scales[i % len(scales)]) for i in range(len(a.payload.source.constraints)))
    s = replace(a.payload.source, constraints=tuple(rows.encode(r,e) for r,e in zip(rs,a.payload.source.constraints)))
    c = replace(a.payload.upper, assumption_terms=tuple(replace(t,weight=t.weight/rs[t.index].scale)
        for t in a.payload.upper.assumption_terms))
    origin = dict(mode='deterministic_regression_fixture', description=
        f'D5 {T}-step exact signed row scales on D4 stored data; nonnegative oriented multipliers, no solver')
    result = rows.Artifact(replace(a,payload=replace(a.payload,source=s,upper=c,origin=origin)),rs,'')
    raw = rows.artifact_tree(result)
    if not rows.diagnose(rows.parse_artifact(raw,T))['diagnostic_passed']:
        raise ArithmeticError('D5 fixture failed exact diagnostics')
    return raw


def generate() -> dict[Path,str]:
    blocks, reports, out = [f'import {rows.AS}\n'], [], {}
    for T,word,namespace in CASES:
        a = rows.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_rows/pg_{word}.json'),T)
        blocks.append(rows.render_module(a,'LeanPEP.Imported.CompositeRows.'+namespace).split('\n',1)[1])
        reports.append(rows.diagnose(a))
        out[ROOT/f'data/fixtures/composite_rows_generated/pg_{word}_normalized.json'] = json.dumps(
            order.artifact_tree(rows.normalized_artifact(a)),indent=2,sort_keys=True)+'\n'
    out[ROOT/'LeanPEP/Imported/CompositeRows.lean'] = '\n'.join(blocks)
    out[ROOT/'data/fixtures/composite_rows_generated/diagnostics.json'] = json.dumps(reports,indent=2,sort_keys=True)+'\n'
    return out


def main() -> None:
    if sys.argv[1:] == ['--create-fixtures']:
        for T,word,_ in CASES:
            path=ROOT/f'data/fixtures/composite_rows/pg_{word}.json'
            gram.atomic_write(path,json.dumps(fixture(T,word=='unit'),indent=2,sort_keys=True)+'\n')
            print(path.relative_to(ROOT))
    elif sys.argv[1:]:
        raise SystemExit('only supported option: --create-fixtures')
    for path,text in generate().items():
        gram.atomic_write(path,text)
        print(path.relative_to(ROOT))


if __name__ == '__main__':
    main()
