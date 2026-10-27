#!/usr/bin/env python3
"""Independent GD1 observer around the unchanged smooth-only capture entry.
One original PEP.solve call; read the wrapper arrays directly after it returns.
No Point.eval, problem.G_value, projection, or second solver call is used here.
"""
import argparse
from pathlib import Path
from unittest.mock import patch
import import_exact_gram_bundle as gram
import capture_pepit_gd_one as original
import capture_pepit_proximal_gradient as decimal
import replay_structured_gd_one as source
import run_pepit_pipeline as pipeline

def capture_pair():
    from PEPit import PEP
    saved=[];solve=PEP.solve
    def observed(problem,*args,**kwargs):
        result=solve(problem,*args,**kwargs)
        G,F=problem.wrapper.get_primal_variables()
        if G is None or F is None or G.shape!=(3,3) or F.shape!=(4,):raise ValueError('wrapper shape')
        saved.append(dict(gram=[[decimal.solver_decimal(G[i,j]) for j in range(3)] for i in range(3)],values=[decimal.solver_decimal(F[i]) for i in range(4)]))
        return result
    with patch.object(PEP,'solve',observed):c=original.capture()
    source.parse(c)
    if len(saved)!=1:raise ValueError('expected exactly one original solve')
    s=dict(format='leanpep-gd1-primal-observation-v1',capture_sha256=gram.canonical_json_sha256(c),source='PEPit.wrapper.get_primal_variables (optimal_G, optimal_F)',basis_order=c['basis_order'],value_order=c['value_order'],tau_index=3,numerical_convention='finite_decimal_strings_v1',point_eval_used=False,projection_performed_by_exporter=False,feasibility_checked=False,lean_checked=False,actual_lower_bound_proved=False,**saved[0])
    return c,s

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    if a.output.exists() and any(a.output.iterdir()):raise SystemExit('output must be new/empty')
    a.output.mkdir(parents=True,exist_ok=True)
    pipeline.write_json(a.output/'environment.json',pipeline.runtime_info('CLARABEL',True))
    c,s=capture_pair()
    pipeline.write_json(a.output/'capture.json',c);pipeline.write_json(a.output/'primal_observation.json',s)
    pipeline.write_json(a.output/'provenance.json',dict(live_capture_performed=True,solve_count=1,capture_byte_sha256=pipeline.digest(a.output/'capture.json'),sidecar_byte_sha256=pipeline.digest(a.output/'primal_observation.json'),capture_canonical_sha256=s['capture_sha256'],observer_sha256=pipeline.digest(Path(__file__)),original_capture_code_sha256=pipeline.digest(Path(original.__file__))))
