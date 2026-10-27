#!/usr/bin/env python3
"""D8 committed decimal regression inputs, explicitly NOT solver captures.

Only --create-fixtures reads old exact accepted examples and truncates them to
finite decimal strings. Normal regeneration reads the committed approximate
inputs and NEVER imports a certificate formula or asks for a known rate.
"""
from __future__ import annotations
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep

ROOT=Path(__file__).resolve().parents[1]
CASES=((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'),(1,'exact','PGExact'))


def decimal_trunc(q: dict[str,int], places: int=12) -> str:
    a,b=q['num'],q['den']
    n=abs(a)*10**places//b
    w,t=divmod(n,10**places)
    suffix=str(t).rjust(places,'0').rstrip('0')
    return ('-' if a<0 and n else '')+str(w)+('.'+suffix if suffix else '')


def candidate_decimals(tree):
    if isinstance(tree,dict):
        if set(tree)=={'num','den'}: return decimal_trunc(tree)
        return {k:candidate_decimals(v) for k,v in tree.items()}
    if isinstance(tree,list): return [candidate_decimals(v) for v in tree]
    return tree


def fixture(T: int, exact: bool=False) -> dict:
    word='all' if exact else {1:'one',2:'two',3:'three'}[T]
    tree=gram.load_json(ROOT/f'data/fixtures/composite_sparse/pg_{word}.json')
    tree['base_source']['origin']={'mode':'deterministic_regression_fixture',
        'description':f'D8 {T}-step finite-decimal regression from D7 exact data; NOT a live capture'}
    c=tree.pop('upper'); c.pop('dual_factor')
    return dict(format=prep.FORMAT,numeric_convention=prep.NUMBERS,source=tree,
        policy=dict(method='limit_denominator',max_denominator=1000,max_abs_error='0.00000000001'),
        upper=candidate_decimals(c))


def generate() -> dict[Path,str]:
    out={}; blocks=[f'import {prep.AS}\n']
    for T,word,name in CASES:
        inp=ROOT/f'data/fixtures/composite_candidates/pg_{word}.json'
        p=prep.prepare(gram.load_json(inp),T)
        blocks.append(prep.render_module(p,'LeanPEP.Imported.CompositeCandidates.'+name).split('\n',1)[1])
        prefix=ROOT/'data/fixtures/composite_candidates_generated'/word
        for path,text in prep.outputs(p,prefix,'LeanPEP.Imported.CompositeCandidates.'+name).items():
            if path.name!='Candidates.lean': out[path]=text
    out[ROOT/'LeanPEP/Imported/CompositeCandidates.lean']='\n'.join(blocks)
    return out


def main() -> None:
    if sys.argv[1:]==['--create-fixtures']:
        for T,word,_ in CASES:
            path=ROOT/f'data/fixtures/composite_candidates/pg_{word}.json'
            gram.atomic_write(path,json.dumps(fixture(T,word=='exact'),indent=2,sort_keys=True)+'\n')
    elif sys.argv[1:]: raise SystemExit('only --create-fixtures is supported')
    for path,text in generate().items():
        gram.atomic_write(path,text)
        print(path.relative_to(ROOT))

if __name__=='__main__': main()
