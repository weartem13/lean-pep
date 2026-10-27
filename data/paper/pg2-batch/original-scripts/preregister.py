from pathlib import Path
import sys,json,hashlib,datetime,importlib.metadata
R=Path.cwd();E=R/'RefineEvidence_001'
from cvxpy.reductions.solvers.conic_solvers.clarabel_conif import CLARABEL
settings=[(1e-8,1e-8,True),(1e-7,1e-10,True),(1e-9,1e-10,True),(1e-6,1e-10,True),(1e-8,1e-9,True),(1e-8,1e-11,True),(1e-8,1e-10,False),(1e-7,1e-9,False)]
config=[]
for i,(reg,tol,equil) in enumerate(settings,1):
 o=dict(max_iter=300,tol_gap_abs=tol,tol_gap_rel=tol,tol_feas=tol,equilibrate_enable=equil,static_regularization_constant=reg)
 obj=CLARABEL.parse_solver_opts(True,o)
 config.append(dict(id=f'B{i:02}',options=o,effective_settings_repr=repr(obj),selection='preplanned reference/regularization/tolerance/equilibration matrix; not random or optimal',legal_options_parsed=True))
versions={n:importlib.metadata.version(n) for n in ['PEPit','cvxpy','clarabel','numpy','scipy']};assert versions['PEPit']=='0.5.1' and versions['cvxpy']=='1.8.2' and versions['clarabel']=='0.11.1'
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
base=json.loads((R/'ReuseEvidence_002/pre_experiment_freeze.json').read_text())['files']
for f,x in base.items():assert h(R/f)==x,f
files={str(f.relative_to(R)):h(f) for f in sorted((R/'LeanPEP').rglob('*.lean'))}
files.update({str(f.relative_to(R)):h(f) for f in sorted((R/'tools').glob('*.py'))})
for f in ['lakefile.lean','lake-manifest.json','lean-toolchain','docs/pg-core-content-review.json']:
 if (R/f).exists():files[f]=h(R/f)
for f in sorted((E/'scripts').glob('*.py')):files[str(f.relative_to(R))]=h(f)
hist=json.loads((R/'ReuseEvidence_002/seen_pg2_inputs.json').read_text());hist.append(dict(path='ReuseEvidence_002/capture_001/capture.json',sha256=h(R/'ReuseEvidence_002/capture_001/capture.json')))
plan=dict(task='LP-PAPER-REFINE-001',frozen_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_id='sha256:e43a0018cd7dd8d202361abcea8fcbbda1db7981bf25ec5e36c317116b1f429c',configurations=config,versions=versions,participating_files=files,historical_inputs=hist,source_profile='PG T=2; L=step=radius=1; single final composite gap',solver_calls=8,solve_wall_limit_seconds=120,candidate_and_source_wall_limit_seconds=120,lean_wall_limit_seconds=900,post_lean_wrapper_allowance_seconds=30,memory_hard_limit=None,memory_limit_explanation='OS-managed 32 GiB machine; no extra reliable per-process RSS cap; processes sequential',consumer_output_root='<WORK_TMP>/LeanPEP_REFINE_BATCH',recovery_rule='unchanged 64 denominators D500000..499937',policy=dict(M=1000000,eta='1/1000000',entries=158,factors='unchanged'),post_output_adaptation='forbidden; no resampling or parameter changes',dedup='exact Fraction of entire numerical object, after symbolic source/basis/value/reference equality; one recovery per distinct payload',observational_instrumentation='sys.setprofile reads completed build_candidate locals/trials without changing functions or results',no_solve_during_option_validation=True)
p=E/'preregistration.json';assert not p.exists();p.write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n');(E/'preregistration.sha256').write_text(h(p)+'\n')
print(json.dumps(dict(configurations=len(config),frozen_files=len(files),versions=versions,preregistration_sha256=h(p),solver_calls_so_far=0)))
