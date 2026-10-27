#!/usr/bin/env python3
"""D3 deterministic native-coordinate regressions, NOT live solver artifacts.

Fixture creation constructs uncentered sample vectors and compiles all component
pairs directly, then computes the independent dual target before D1 synthesis.
Normal regeneration only reads the committed inputs; it never repairs them.
"""
from __future__ import annotations

import json
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import sys

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as src
import import_proximal_gradient_coordinates as coords
import regenerate_proximal_gradient_source as previous
import synthesize_psd_factors as psd

ROOT = Path(__file__).resolve().parents[1]


def native_snapshot(T: int) -> src.Snapshot:
    p,m,q=coords.dimensions(T)
    star=src.unit(q,0)
    xs=[src.unit(q,1)]
    for k in range(T):
        xs.append(src.vsub(src.vsub(xs[-1],src.unit(q,3+k)),src.unit(q,T+4+k)))
    sm=(src.Sample(0,star,src.unit(q,2)),)+tuple(src.Sample(k+1,xs[k],src.unit(q,3+k)) for k in range(T+1))
    ns=(src.Sample(T+2,star,tuple(-t for t in src.unit(q,2))),)+tuple(
        src.Sample(T+3+k,xs[k+1],src.unit(q,T+4+k)) for k in range(T))
    cs=tuple(src.pair(p,True,a,b) for a in sm for b in sm)+tuple(src.pair(p,False,a,b) for a in ns for b in ns)
    radius=src.add(replace(src.zero(p,q),const=Q(1)),src.scale(Q(-1),src.bilinear(p,src.vsub(xs[0],star),src.vsub(xs[0],star))))
    obj=src.add(src.add(src.value(p,q,T+1),src.value(p,q,p-1)),src.scale(Q(-1),src.add(src.value(p,q,0),src.value(p,q,T+2))))
    return src.Snapshot(coords.expected_header(T),sm,ns,cs+(radius,),obj)


def fixture(T: int) -> dict:
    s=native_snapshot(T)
    old=src.parse_artifact(previous.fixture(T))
    p,m,q=coords.dimensions(T)
    residual=src.add(replace(src.zero(p,q),const=old.upper.bound),src.scale(Q(-1),s.objective))
    for term in old.upper.assumption_terms:
        residual=src.add(residual,src.scale(-term.weight,s.constraints[term.index]))
    if residual.const or any(residual.value_coeff):
        raise ArithmeticError('native certificate did not cancel value/constant coefficients')
    S=residual.gram_coeff
    fs=psd.synthesize_psd(S)
    if fs.status!='psd' or not psd.verify_result(S,fs):
        raise ArithmeticError('independent native dual matrix is not exactly PSD')
    c=gram.UpperSpec(old.upper.bound,s.objective,(),old.upper.assumption_terms,S,
        gram.FactorCertSpec(tuple(gram.RankOneFactorSpec(f.weight,f.vector) for f in fs.factors)))
    C,J=coords.maps(m)
    st=src.source_tree(s)
    st.update(center_matrix=C,section_matrix=J)
    raw=src.exact_json(dict(format=coords.FORMAT,horizon=T,
        origin=dict(mode='deterministic_regression_fixture',
            description=f'D3 uncentered {T}-step PG; direct native sample compilation, no solver call'),
        source=st,upper=coords.upper_tree(c)))
    a=coords.parse_artifact(raw,T)
    if not coords.diagnose(a)['diagnostic_passed']:
        raise ArithmeticError('created fixture failed exact diagnostic')
    return raw


def generate() -> dict[Path,str]:
    blocks=[f'import {coords.AS}\n']
    reports=[]
    out={}
    for T,word,ns in ((1,'one','PGOne'),(2,'two','PGTwo'),(3,'three','PGThree')):
        a=coords.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_coordinates/pg_{word}_step.json'),T)
        blocks.append(coords.render_module(a,'LeanPEP.Imported.CompositeCoordinates.'+ns).split('\n',1)[1])
        reports.append(coords.diagnose(a))
        out[ROOT/f'data/fixtures/composite_coordinates_generated/pg_{word}_centered.json']=json.dumps(coords.centered_json(a),indent=2,sort_keys=True)+'\n'
    out[ROOT/'LeanPEP/Imported/CompositeCoordinates.lean']='\n'.join(blocks)
    out[ROOT/'data/fixtures/composite_coordinates_generated/diagnostics.json']=json.dumps(reports,indent=2,sort_keys=True)+'\n'
    return out


def main() -> None:
    if sys.argv[1:]==['--create-fixtures']:
        for T,word in ((1,'one'),(2,'two'),(3,'three')):
            p=ROOT/f'data/fixtures/composite_coordinates/pg_{word}_step.json'
            gram.atomic_write(p,json.dumps(fixture(T),indent=2,sort_keys=True)+'\n')
            print(p.relative_to(ROOT))
    elif sys.argv[1:]:
        raise SystemExit('Only optional argument: --create-fixtures')
    for p,text in generate().items():
        gram.atomic_write(p,text)
        print(p.relative_to(ROOT))


if __name__=='__main__':
    main()
