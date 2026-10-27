#!/usr/bin/env python3
"""One recorded GD1 solve, observing original wrapper arrays; old defaults unchanged."""
from pathlib import Path
from unittest.mock import patch
import argparse,time
import capture_pepit_gd_one as original
import capture_pepit_proximal_gradient as decimal
import replay_structured_gd_one as source
import import_exact_gram_bundle as gram
import run_pepit_pipeline as pipe
OPTIONS=dict(tol_gap_abs=1e-12,tol_gap_rel=1e-12,tol_feas=1e-12,max_iter=500)

def capture_pair(options):
    from PEPit import PEP
    solve=PEP.solve;saved=[]
    def observed(problem,*args,**kwargs):
        kwargs.update(options)
        start=time.monotonic();result=solve(problem,*args,**kwargs);elapsed=time.monotonic()-start
        G,F=problem.wrapper.get_primal_variables()
        if G is None or F is None or G.shape!=(3,3) or F.shape!=(4,):raise ValueError('wrapper shape')
        saved.append(dict(gram=[[decimal.solver_decimal(G[i,j]) for j in range(3)] for i in range(3)],values=[decimal.solver_decimal(F[i]) for i in range(4)],effective_solve_kwargs=dict(kwargs),elapsed_seconds=elapsed))
        return result
    with patch.object(PEP,'solve',observed):c=original.capture()
    if len(saved)!=1:raise ValueError('one solve required')
    observed_data=saved[0];effective=observed_data.pop('effective_solve_kwargs');elapsed=observed_data.pop('elapsed_seconds')
    # Original capture local options describe its default call. Replace only this
    # producer metadata with the options actually passed by this independent entry.
    c['producer']['options']=dict(options)
    source.parse(c)
    s=dict(format='leanpep-gd1-primal-observation-v1',capture_sha256=gram.canonical_json_sha256(c),source='PEPit.wrapper.get_primal_variables (optimal_G, optimal_F)',basis_order=c['basis_order'],value_order=c['value_order'],tau_index=3,numerical_convention='finite_decimal_strings_v1',point_eval_used=False,projection_performed_by_exporter=False,feasibility_checked=False,lean_checked=False,actual_lower_bound_proved=False,**observed_data)
    return c,s,dict(effective_solve_kwargs=effective,solve_elapsed_seconds=elapsed)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if a.output.exists():raise SystemExit('new directory required')
    a.output.mkdir(parents=True)
    env=pipe.runtime_info('CLARABEL',True);env['effective_solver_options']=OPTIONS;pipe.write_json(a.output/'environment.json',env)
    c,s,info=capture_pair(OPTIONS)
    pipe.write_json(a.output/'capture.json',c);pipe.write_json(a.output/'primal_observation.json',s)
    pipe.write_json(a.output/'provenance.json',dict(live_capture_performed=True,solve_count=1,effective_solver_options=OPTIONS,capture_byte_sha256=pipe.digest(a.output/'capture.json'),sidecar_byte_sha256=pipe.digest(a.output/'primal_observation.json'),capture_canonical_sha256=s['capture_sha256'],observer_sha256=pipe.digest(Path(__file__)),original_capture_code_sha256=pipe.digest(Path(original.__file__)),**info))
