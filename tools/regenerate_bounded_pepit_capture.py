#!/usr/bin/env python3
"""D11 offline simulations. Only --create-fixtures constructs test captures.
The ordinary path reads committed captures and never calls a solver/formula.
"""
from __future__ import annotations
import json
from pathlib import Path
import sys
import import_exact_gram_bundle as gram
import import_proximal_gradient_source as src
import import_proximal_gradient_coordinates as coord
import complete_bounded_pepit_capture as comp

ROOT=Path(__file__).resolve().parents[1]
CASES=((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'),(1,'budget','Budget'))


def fixture(word: str) -> dict:
    original='one' if word=='budget' else word
    d=gram.load_json(ROOT/f'data/fixtures/pepit_completion/pg_{original}.json')
    if word=='budget':
        d['numerical']['bound']='0.2531'
    else:
        # An explicitly RETAINED constant-zero self-pair (allowed by D7/D9).
        # The tiny negative weight is a FREE variable: no coefficient equation
        # forces it to zero. This is a simulated diagnostic, NOT live PEPit.
        p,m=len(d['value_order']),len(d['basis_order'])
        d['constraints'].append(dict(name='D11_SIMULATED_retained_self_pair',
            label=dict(kind='base',tag=dict(kind='smoothPair',i=0,j=0)),
            sense='leZero',expression=coord.expr_tree(src.zero(p,m))))
        d['numerical']['multipliers'].append('-0.0001')
    assert d['producer']['mode']=='simulated_regression'
    return src.exact_json(d)


def generate() -> dict[Path,str]:
    out={};blocks=[f'import {comp.old.AS}\nimport {comp.BS}\n']
    for T,word,name in CASES:
        a=comp.complete(gram.load_json(ROOT/f'data/fixtures/pepit_bounded/pg_{word}.json'),T)
        namespace='LeanPEP.Imported.CompositeBoundedCompletion.'+name
        block=comp.render_module(a,namespace)
        blocks.append(block.split('\n',2)[2])
        for p,t in comp.outputs(a,ROOT/f'data/fixtures/pepit_bounded_generated/{word}',namespace).items():
            if p.suffix!='.lean' and p.name not in ('capture_input.json','source.json'):
                out[p]=t
    out[ROOT/'LeanPEP/Imported/CompositeBoundedCompletion.lean']='\n'.join(blocks)
    return out


def main() -> None:
    if sys.argv[1:]==['--create-fixtures']:
        for _,word,_ in CASES:
            gram.atomic_write(ROOT/f'data/fixtures/pepit_bounded/pg_{word}.json',json.dumps(fixture(word),indent=2,sort_keys=True)+'\n')
    elif sys.argv[1:]:raise SystemExit('only --create-fixtures is supported')
    for p,t in generate().items():gram.atomic_write(p,t);print(p.relative_to(ROOT))

if __name__=='__main__':main()
