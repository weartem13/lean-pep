#!/usr/bin/env python3
"""D9 OFFLINE protocol fixtures. --create-fixtures uses old exact D7 data.
Normal regeneration only reads committed captures; it NEVER calls a solver.
These fixtures test serialization/auditing, not the actual PEPit runtime.
"""
from __future__ import annotations
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_coordinates as native
import import_proximal_gradient_ordering as order
import import_proximal_gradient_rows as rows
import import_proximal_gradient_performance as perf
import import_proximal_gradient_sparse as sparse
import import_pepit_proximal_gradient_capture as cap
import regenerate_proximal_gradient_candidates as old_fixture

ROOT=Path(__file__).resolve().parents[1]
CASES=((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree'))


def fixture(T: int) -> dict:
    word={1:'one',2:'two',3:'three'}[T]
    a=sparse.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_sparse/pg_{word}.json'),T)
    b=a.base.ordered.payload.source; p=len(a.objective.value_coeff);m=len(a.objective.gram_coeff)
    # Move tau from the adapter's slot0 to the LAST original scalar leaf.
    forward=order.index_map(tuple(list(range(1,p))+[0])); ident=order.index_map(tuple(range(m)))
    move=lambda e:order.expr(forward,ident,e)
    def sample(ss,axis):
        return [dict(logical_index=a.base.ordered.ordering[axis].to_canonical[i],
            value_index=s.value_index,position=s.position,oracle=s.oracle) for i,s in enumerate(ss)]
    cs=[];weights=[Q(0)]*len(a.compact_rows)
    for t in a.upper.assumption_terms: weights[t.index]+=t.weight*a.compact_rules[t.index].scale
    for i,e in enumerate(a.compact_rows):
        q=centered.scale(-1,rows.normalize(a.compact_rules[i],e))
        cs.append(dict(name=f'SIMULATED_row_{i}',label=a.compact_labels[i],sense='leZero',expression=native.expr_tree(move(q))))
    dec=lambda q:old_fixture.decimal_trunc(dict(num=q.numerator,den=q.denominator))
    return centered.exact_json(dict(format=cap.FORMAT,producer=dict(name='PEPit',version=cap.SUPPORTED_PEPIT,
        mode='simulated_regression',wrapper='not_run',solver='not_run',status='not_run'),horizon=T,
        profile=dict(smooth_class='SmoothConvexFunction',nonsmooth_class='ConvexFunction',L=Q(1),step_size=Q(1),radius_squared=Q(1)),
        basis_order=b.header['basis_order'],value_order=list(b.header['value_order'])+['tau'],
        smooth_samples=sample(b.smooth_samples,'smooth'),nonsmooth_samples=sample(b.nonsmooth_samples,'nonsmooth'),
        metric=native.expr_tree(move(perf.embed(b.objective))),objective=native.expr_tree(move(a.objective)),constraints=cs,
        numerical=dict(bound=dec(a.upper.bound),multipliers=list(map(dec,weights)),
            residual=[[dec(q) for q in r] for r in a.upper.dual_matrix]),
        policy=dict(method='limit_denominator',max_denominator=1000,max_abs_error='0.00000000001')))


def generate() -> dict[Path,str]:
    out={};blocks=[f'import {cap.AS}\n']
    for T,word,name in CASES:
        inp=ROOT/f'data/fixtures/pepit_capture/pg_{word}.json'
        c=cap.convert(gram.load_json(inp),T)
        ns='LeanPEP.Imported.CompositeCapture.'+name
        blocks.append(cap.render_module(c,ns).split('\n',1)[1])
        # Retain reports and exact candidates for independent replay.
        for p,t in cap.outputs(c,ROOT/f'data/fixtures/pepit_capture_generated/{word}',ns).items():
            if p.suffix!='.lean' and p.name!='capture_input.json': out[p]=t
    out[ROOT/'LeanPEP/Imported/CompositeCapture.lean']='\n'.join(blocks)
    return out


def main():
    if sys.argv[1:]==['--create-fixtures']:
        for T,word,_ in CASES:
            gram.atomic_write(ROOT/f'data/fixtures/pepit_capture/pg_{word}.json',json.dumps(fixture(T),indent=2,sort_keys=True)+'\n')
    elif sys.argv[1:]: raise SystemExit('only --create-fixtures is supported')
    for p,t in generate().items(): gram.atomic_write(p,t);print(p.relative_to(ROOT))

if __name__=='__main__':main()
