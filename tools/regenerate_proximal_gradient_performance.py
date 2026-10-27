#!/usr/bin/env python3
"""D6 regression artifacts, NOT live capture. Normal regeneration reads committed
submitted inputs only. --create-fixtures is explicit and uses the old D5 fixtures.
"""
from __future__ import annotations
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_rows as rows
import import_proximal_gradient_performance as perf

ROOT=Path(__file__).resolve().parents[1]
CASES=((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'),(1,'unit','PGUnit'))


def fixture(T: int, unit: bool=False) -> dict:
    word='unit' if unit else {1:'one',2:'two',3:'three'}[T]
    b=rows.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_rows/pg_{word}.json'),T)
    payload=b.ordered.payload
    rule=rows.Rule('geZero' if unit else 'leZero',Q(1) if unit else Q(T+1,T+2))
    obj=perf.tau(len(payload.source.objective.value_coeff),len(payload.source.objective.gram_coeff))
    es=(rows.encode(rule,perf.link(payload.source.objective)),)+tuple(map(perf.embed,payload.source.constraints))
    terms=tuple(replace(t,index=t.index+1) for t in payload.upper.assumption_terms)
    # Deliberately split the link multiplier in PGTwo: it is the TOTAL weighted
    # mass which equals one. Reference order and duplicate terms are retained.
    if T==2 and not unit:
        links=(gram.AssumptionTermSpec(Q(1)/(3*rule.scale),0),gram.AssumptionTermSpec(Q(2)/(3*rule.scale),0))
        terms=links[:1]+terms[:2]+links[1:]+terms[2:]
    else:
        terms=(gram.AssumptionTermSpec(Q(1)/rule.scale,0),)+terms
    upper=replace(payload.upper,objective=obj,assumption_terms=terms)
    origin=dict(mode='deterministic_regression_fixture',description=
        f'D6 {T}-step exact single-performance lifting of D5 data; no solver, tau is not a Gram vector')
    b=replace(b,ordered=replace(b.ordered,payload=replace(payload,origin=origin)))
    a=perf.Artifact(b,rule,es,obj,upper,'')
    raw=perf.artifact_tree(a)
    if not perf.diagnose(perf.parse_artifact(raw,T))['diagnostic_passed']:
        raise ArithmeticError('D6 fixture failed exact diagnostics')
    return raw


def generate() -> dict[Path,str]:
    out,blocks,reports={},[f'import {perf.AS}\n'],[]
    for T,word,namespace in CASES:
        a=perf.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_performance/pg_{word}.json'),T)
        blocks.append(perf.render_module(a,'LeanPEP.Imported.CompositePerformance.'+namespace).split('\n',1)[1])
        reports.append(perf.diagnose(a))
        out[ROOT/f'data/fixtures/composite_performance_generated/pg_{word}_base.json']=json.dumps(
            rows.artifact_tree(perf.eliminated_artifact(a)),indent=2,sort_keys=True)+'\n'
    out[ROOT/'LeanPEP/Imported/CompositePerformance.lean']='\n'.join(blocks)
    out[ROOT/'data/fixtures/composite_performance_generated/diagnostics.json']=json.dumps(reports,indent=2,sort_keys=True)+'\n'
    return out


def main() -> None:
    if sys.argv[1:]==['--create-fixtures']:
        for T,word,_ in CASES:
            path=ROOT/f'data/fixtures/composite_performance/pg_{word}.json'
            gram.atomic_write(path,json.dumps(fixture(T,word=='unit'),indent=2,sort_keys=True)+'\n')
            print(path.relative_to(ROOT))
    elif sys.argv[1:]:
        raise SystemExit('only supported option: --create-fixtures')
    for path,text in generate().items():
        gram.atomic_write(path,text)
        print(path.relative_to(ROOT))


if __name__=='__main__':
    main()
