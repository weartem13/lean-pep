#!/usr/bin/env python3
"""D4 deterministic ordering fixtures, explicitly NOT live PEPit captures.

Fixture creation permutes the independent D3 inputs and their D1 factors.
Normal regeneration only reads committed inputs. It does not infer, repair,
reconstruct, or synthesize any arrays supplied by those inputs.
"""
from __future__ import annotations

from dataclasses import replace
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_coordinates as native
import import_proximal_gradient_ordering as order
import regenerate_proximal_gradient_coordinates as previous

ROOT = Path(__file__).resolve().parents[1]
CASES = ((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'),(1,'identity','PGIdentity'))


def fixture(T: int, identity: bool=False) -> dict:
    a = native.parse_artifact(previous.fixture(T),T)
    offsets = dict(basis=2,values=1,smooth=1,nonsmooth=1,rows=3)
    o = {k:order.index_map(tuple((i+(0 if identity else offsets[k])) % size for i in range(size)))
         for k,size in order.dimensions(T).items()}
    a = replace(a,origin=dict(mode='deterministic_regression_fixture',
        description=f'D4 {T}-step exact PG storage permutations; D3 source and D1 factors, no solver call'))
    external = order.transport(a,{k:p.inverse() for k,p in o.items()})
    raw = order.artifact_tree(order.Artifact(external,o,''))
    parsed = order.parse_artifact(raw,T)
    if not order.diagnose(parsed)['diagnostic_passed']:
        raise ArithmeticError('new fixture did not pass exact independent diagnostics')
    return raw


def generate() -> dict[Path,str]:
    out = {}
    blocks = [f'import {order.AS}\n']
    reports = []
    for T,word,namespace in CASES:
        a = order.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_ordering/pg_{word}.json'),T)
        blocks.append(order.render_module(a,'LeanPEP.Imported.CompositeOrdering.'+namespace).split('\n',1)[1])
        reports.append(order.diagnose(a))
        out[ROOT/f'data/fixtures/composite_ordering_generated/pg_{word}_native.json'] = (
            json.dumps(order.native_tree(order.canonical_native(a)),indent=2,sort_keys=True)+'\n')
    out[ROOT/'LeanPEP/Imported/CompositeOrdering.lean'] = '\n'.join(blocks)
    out[ROOT/'data/fixtures/composite_ordering_generated/diagnostics.json'] = json.dumps(reports,indent=2,sort_keys=True)+'\n'
    return out


def main() -> None:
    if sys.argv[1:]==['--create-fixtures']:
        for T,word,_ in CASES:
            path=ROOT/f'data/fixtures/composite_ordering/pg_{word}.json'
            gram.atomic_write(path,json.dumps(fixture(T,word=='identity'),indent=2,sort_keys=True)+'\n')
            print(path.relative_to(ROOT))
    elif sys.argv[1:]:
        raise SystemExit('only supported option: --create-fixtures')
    for p,text in generate().items():
        gram.atomic_write(p,text)
        print(p.relative_to(ROOT))


if __name__=='__main__':
    main()
