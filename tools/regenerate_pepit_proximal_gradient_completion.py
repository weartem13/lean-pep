#!/usr/bin/env python3
"""D10 offline completion fixtures, not solver outputs.
Only --create-fixtures derives controlled perturbations from D9 simulations.
Normal regeneration reads committed inputs; never reads a certificate formula.
"""
from __future__ import annotations
from decimal import Decimal, localcontext
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import complete_pepit_proximal_gradient_capture as comp

ROOT = Path(__file__).resolve().parents[1]
CASES = ((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'),(1,'inconsistent','Inconsistent'))


def fixture(word: str) -> dict:
    source_word = 'one' if word == 'inconsistent' else word
    d = gram.load_json(ROOT / f'data/fixtures/pepit_capture/pg_{source_word}.json')
    with localcontext() as ctx:
        ctx.prec = 100
        plus = lambda x: str(Decimal(x) + Decimal('0.0001'))
        d['numerical']['bound'] = plus(d['numerical']['bound'])
        d['numerical']['multipliers'][0] = plus(d['numerical']['multipliers'][0])
        if word == 'inconsistent':
            # A PSD positive perturbation of source-basis diagonal entry 0.
            # The fixed-target coefficient equations cannot absorb it.
            d['numerical']['residual'][0][0] = plus(d['numerical']['residual'][0][0])
    d['policy'] = dict(method='limit_denominator', max_denominator=10000, max_abs_error='0.001')
    assert d['producer']['mode'] == 'simulated_regression'
    return d


def generate() -> dict[Path,str]:
    out = {}
    blocks = [f'import {comp.AS}\n']
    for T,word,name in CASES:
        a = comp.complete(gram.load_json(ROOT / f'data/fixtures/pepit_completion/pg_{word}.json'),T)
        ns = 'LeanPEP.Imported.CompositeCompletion.' + name
        blocks.append(comp.render_module(a,ns).split('\n',1)[1])
        for p,t in comp.outputs(a, ROOT / f'data/fixtures/pepit_completion_generated/{word}', ns).items():
            if p.suffix != '.lean' and p.name not in ('capture_input.json','source.json'):
                out[p] = t
    out[ROOT / 'LeanPEP/Imported/CompositeCompletion.lean'] = '\n'.join(blocks)
    return out


def main() -> None:
    if sys.argv[1:] == ['--create-fixtures']:
        for _,word,_ in CASES:
            gram.atomic_write(ROOT / f'data/fixtures/pepit_completion/pg_{word}.json',
                json.dumps(fixture(word),indent=2,sort_keys=True)+'\n')
    elif sys.argv[1:]:
        raise SystemExit('only --create-fixtures is supported')
    for p,t in generate().items():
        gram.atomic_write(p,t)
        print(p.relative_to(ROOT))

if __name__ == '__main__': main()
