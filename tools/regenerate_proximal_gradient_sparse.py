#!/usr/bin/env python3
"""D7 exact regression input creation is opt-in. Default regeneration reads
committed sparse inputs; no solver/capture and no replacement by known bounds.
"""
from __future__ import annotations
from dataclasses import replace
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_performance as perf
import import_proximal_gradient_sparse as sparse

ROOT=Path(__file__).resolve().parents[1]
CASES=((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'),(1,'all','PGAll'))


def compact(a: perf.Artifact, keep: tuple[int,...]) -> sparse.Artifact:
    """Fixture-only construction; removal is explicit and requires zero rows.
    References to omitted zero polynomials may be discarded in creating a new
    submitted certificate. The D7 importer itself never drops a supplied term.
    """
    r=len(a.extended_rows)
    if len(set(keep))!=len(keep) or any(i<0 or i>=r for i in keep): raise ValueError('invalid keep set')
    inverse=[None]*r
    for i,j in enumerate(keep): inverse[j]=i
    if any(inverse[j] is None and not sparse.is_zero(e) for j,e in enumerate(a.extended_rows)):
        raise ValueError('cannot create a positive fixture by removing a nonzero row')
    c=replace(a.upper,assumption_terms=tuple(replace(t,index=inverse[t.index])
        for t in a.upper.assumption_terms if inverse[t.index] is not None))
    labels=sparse.expected_labels(a.base); rules=(a.performance_rule,)+a.base.rules
    return sparse.Artifact(a.base,a.performance_rule,sparse.Coverage(keep,tuple(inverse)),
        tuple(a.extended_rows[j] for j in keep),tuple(rules[j] for j in keep),
        tuple(labels[j] for j in keep),a.objective,c,'')


def fixture(T:int,all_rows:bool=False) -> dict:
    word='unit' if all_rows else {1:'one',2:'two',3:'three'}[T]
    a=perf.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_performance/pg_{word}.json'),T)
    keep=tuple(range(len(a.extended_rows))) if all_rows else tuple(
        j for j,e in enumerate(a.extended_rows) if not sparse.is_zero(e))
    # Independent shorter storage order; even the performance row moves.
    if not all_rows: keep=keep[1:]+keep[:1]
    a=replace(a,base=replace(a.base,ordered=replace(a.base.ordered,payload=replace(a.base.ordered.payload,
        origin=dict(mode='deterministic_regression_fixture',description=f'D7 {T}-step zero-row coverage; not PEPit capture')))))
    b=compact(a,keep)
    raw=sparse.artifact_tree(b)
    if not sparse.diagnose(sparse.parse_artifact(raw,T))['diagnostic_passed']:
        raise ArithmeticError('D7 positive fixture failed')
    return raw


def generate() -> dict[Path,str]:
    out={}; blocks=[f'import {sparse.AS}\n']; reports=[]
    for T,word,ns in CASES:
        a=sparse.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_sparse/pg_{word}.json'),T)
        blocks.append(sparse.render_module(a,'LeanPEP.Imported.CompositeSparse.'+ns).split('\n',1)[1])
        reports.append(sparse.diagnose(a))
        out[ROOT/f'data/fixtures/composite_sparse_generated/pg_{word}_completed.json']=json.dumps(
            perf.artifact_tree(sparse.completed_artifact(a)),indent=2,sort_keys=True)+'\n'
    out[ROOT/'LeanPEP/Imported/CompositeSparse.lean']='\n'.join(blocks)
    out[ROOT/'data/fixtures/composite_sparse_generated/diagnostics.json']=json.dumps(reports,indent=2,sort_keys=True)+'\n'
    return out


def main() -> None:
    if sys.argv[1:]==['--create-fixtures']:
        for T,word,_ in CASES:
            path=ROOT/f'data/fixtures/composite_sparse/pg_{word}.json'
            gram.atomic_write(path,json.dumps(fixture(T,word=='all'),indent=2,sort_keys=True)+'\n')
    elif sys.argv[1:]: raise SystemExit('only --create-fixtures is supported')
    for p,text in generate().items():
        gram.atomic_write(p,text)
        print(p.relative_to(ROOT))

if __name__=='__main__': main()
