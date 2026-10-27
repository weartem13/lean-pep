"""Bounded outer execution, byte-preserving dedup; no mathematical producer changes."""
from pathlib import Path
from fractions import Fraction
import os,json,hashlib,subprocess,time,signal,datetime,sys,resource,shutil
ROOT=Path(__file__).resolve().parents[2];E=ROOT/'RefineEvidence_001'
def write(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def exact_tree(x):
 if isinstance(x,dict):return {k:exact_tree(v) for k,v in sorted(x.items())}
 if isinstance(x,list):return [exact_tree(v) for v in x]
 q=Fraction(str(x));return [q.numerator,q.denominator]
def numerical_key(c):return hashlib.sha256(json.dumps(exact_tree(c['numerical']),sort_keys=True,separators=(',',':')).encode()).hexdigest()
def source_key(c):
 x={k:v for k,v in c.items() if k not in ['numerical','producer']}
 return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def guarded_run(argv,cwd,log,limit,phase_observer=None,env=None):
 started=time.monotonic();at=datetime.datetime.now(datetime.timezone.utc).isoformat()
 command_env=os.environ.copy();command_env.pop('LEAN_PATH',None);command_env.pop('PYTHONPATH',None);command_env['PYTHONDONTWRITEBYTECODE']='1'
 if env:command_env.update(env)
 deadline=started+limit;lean_seen=False;timeout_stage=None
 with log.open('w') as out:
  proc=subprocess.Popen(argv,cwd=cwd,env=command_env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
  while proc.poll() is None:
   if phase_observer and phase_observer.exists() and not lean_seen:
    lean_seen=True;deadline=time.monotonic()+930
   if time.monotonic()>deadline:
    timeout_stage='lean_or_finalization' if lean_seen else 'candidate_or_source' if phase_observer else 'command'
    os.killpg(proc.pid,signal.SIGKILL);proc.wait();break
   time.sleep(.10)
 code=124 if timeout_stage else proc.returncode
 rss=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
 return dict(argv=argv,cwd=str(cwd),exit=code,wall_seconds=time.monotonic()-started,started_at_utc=at,
  log=str(log.relative_to(ROOT)) if log.is_relative_to(ROOT) else str(log),timeout_stage=timeout_stage,
  outer_CHILDREN_high_water_bytes=rss if sys.platform=='darwin' else rss*1024,resource_scope='cumulative CHILDREN high water in batch parent; not per-operation simultaneous peak',
  environment={'LEAN_PATH':'unset','PYTHONPATH':'unset'})
def verify_freeze(f):
 for p,h in f['participating_files'].items():
  if digest(ROOT/p)!=h:raise RuntimeError('frozen file changed: '+p)
def classify(output,observer):
 if (output/'result.json').exists():r=json.loads((output/'result.json').read_text())
 else:r=dict(status='not_completed',actual_upper_verified=False)
 o=json.loads(observer.read_text()) if observer.exists() else {}
 trials=o.get('trials',[])
 return dict(consumer_result=r,observed_candidate=o,counts=dict(
  grids_observed=len(trials),
  policy_rejected=sum(not all(t['policy_checks'].values()) for t in trials),
  nonnegative_rejected=sum(not t['nonnegative_weights'] for t in trials),
  psd_rejected=sum('psd' in t and t['psd']['status']!='psd' for t in trials),
  original_upper_rejected=sum(t.get('original_upper_accepted') is False for t in trials)),
  absent_stage_evidence='unknown or not reached; never inferred from solver status')
def main():
 plan=E/'preregistration.json';f=json.loads(plan.read_text());verify_freeze(f)
 runs=E/'batch';runs.mkdir()
 historical={}
 for ent in f['historical_inputs']:
  c=json.loads((ROOT/ent['path']).read_text());historical.setdefault(numerical_key(c),[]).append(ent['path'])
 reference=json.loads((ROOT/'ReuseEvidence_002/capture_001/capture.json').read_text());sk=source_key(reference)
 records=[];unique={}
 for cfg in f['configurations']:
  verify_freeze(f);out=runs/cfg['id'];out.mkdir()
  argv=[str(ROOT/'.venv-pepit/bin/python'),'tools/capture_pepit_proximal_gradient.py','--steps','2','--solver','CLARABEL','--solver-options',json.dumps(cfg['options']), '--verbose','2','--output',str(out/'capture.json')]
  rec=guarded_run(argv,ROOT,out/'solver.log',120);write(out/'capture-command.json',rec)
  row=dict(id=cfg['id'],configuration=cfg['options'],capture_command=rec)
  if rec['exit']==0 and (out/'capture.json').exists():
   c=json.loads((out/'capture.json').read_text());key=numerical_key(c)
   row.update(capture_sha256=digest(out/'capture.json'),source_matches_reference=source_key(c)==sk,numerical_key=key,producer=c['producer'],historical_matches=historical.get(key,[]))
   if row['source_matches_reference']:
    if key not in unique:unique[key]=cfg['id']
    row['unique_recovery_owner']=unique[key]
   else:row['stage']='source_mismatch'
  else:row['stage']='capture_failed_or_limit'
  records.append(row);write(out/'capture-result.json',row);write(E/'batch-progress.json',records)
  print('captured',cfg['id'],rec['exit'],flush=True)
 # One deterministic recovery per distinct full numerical payload, sequential Lean.
 for key,owner in unique.items():
  verify_freeze(f);d=runs/owner;out=Path(f['consumer_output_root'])/owner;obs=d/'observer.json'
  argv=[sys.executable,str(E/'scripts/observe_consumer.py'),str(ROOT),str(obs),'recover','--source-root',str(ROOT),'--input',str(d/'capture.json'),'--output',str(out),'--namespace','LeanPEP.Imported.Refine001.'+owner,'--timeout','900']
  rec=guarded_run(argv,ROOT,d/'consumer-cli.log',120,phase_observer=out/'Replay.lean')
  detail=classify(out,obs);detail['command']=rec
  if out.exists():shutil.copytree(out,d/'recover')
  write(d/'recovery-result.json',detail)
  for row in records:
   if row.get('numerical_key')==key:row['recovery']=detail;row['recovery_executed_here']=row['id']==owner
  write(E/'batch-progress.json',records);print('recovered',owner,rec['exit'],detail['counts'],flush=True)
 verify_freeze(f)
 summary=dict(configurations=len(records),successful_captures=sum(r['capture_command']['exit']==0 for r in records),different_payloads=len(unique),
  accepted_unique=sum(next(r for r in records if r['id']==owner).get('recovery',{}).get('consumer_result',{}).get('actual_upper_verified',False) for owner in unique.values()),
  historical_payload_count=len(historical),preregistration_sha256=digest(plan),post_freeze_recovery_adaptations=0,records=records)
 write(E/'batch-results.json',summary);print(json.dumps({k:v for k,v in summary.items() if k!='records'}),flush=True)
if __name__=='__main__':main()

