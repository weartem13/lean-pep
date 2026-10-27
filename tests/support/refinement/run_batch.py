"""Retained bounded-batch observation helpers; no solver entry point.

Copied from the accepted refinement harness. These maintenance tests exercise
exact-payload deduplication, stage reporting and process timeouts.
"""
from pathlib import Path
from fractions import Fraction
import os,json,hashlib,subprocess,time,signal,datetime,sys,resource,shutil
ROOT=Path(__file__).resolve().parents[3]
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