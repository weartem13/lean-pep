#!/usr/bin/env python3
"""List or execute the complete, staged maintenance checks; outputs stay outside source."""
from pathlib import Path
import argparse,json,os,subprocess,sys,time,signal,re
ROOT=Path(__file__).resolve().parents[1]
STANDARD_AXIOMS={'propext','Classical.choice','Quot.sound'}

def project_closure(root,module):
 result=set()
 def visit(name):
  if (name!='LeanPEP' and not name.startswith('LeanPEP.')) or name in result:return
  path=root/(name.replace('.','/')+'.lean')
  if not path.is_file():raise ValueError('missing project module: '+name)
  result.add(name)
  for line in re.findall(r'^\s*import ([^\n]+)',path.read_text(),re.M):
   for dependency in line.split():visit(dependency)
 visit(module);return result

def validate_checklist(root,c):
 if c.get('schema')!='leanpep-maintenance-checklist-v1':raise ValueError('unknown maintenance checklist')
 modules={'.'.join(path.relative_to(root).with_suffix('').parts) for path in (root/'LeanPEP').rglob('*.lean')}
 aggregate=project_closure(root,c['aggregate'])
 if len(modules)!=c['expected_library_modules']:raise ValueError('library inventory changed; review the checklist')
 uncovered=modules-aggregate
 if set(c['unaggregated_modules'])!=uncovered:raise ValueError('unaggregated module coverage differs')
 for key in ['prerequisites','sequential_regressions','unaggregated_modules']:
  if len(c[key])!=len(set(c[key])) or not set(c[key])<=modules:raise ValueError('invalid module list: '+key)
 for key in ['smoke_files','regression_files','replay_files']:
  if len(c[key])!=len(set(c[key])):raise ValueError('duplicate file in '+key)
  for name in c[key]:
   path=root/name
   if Path(name).is_absolute() or '..' in Path(name).parts or not path.is_file() or path.is_symlink():raise ValueError('missing/unsafe check file: '+name)
 smokes={p.relative_to(root).as_posix() for p in (root/'tests/lean/smoke').glob('*.lean')}
 regressions={p.relative_to(root).as_posix() for p in (root/'tests/lean/regression').glob('*.lean')}
 case_replays={p.relative_to(root).as_posix() for p in (root/'data/cases').rglob('*.lean')}
 if len(smokes)!=c['expected_smoke_files'] or set(c['smoke_files'])!=smokes:raise ValueError('smoke coverage differs')
 if set(c['regression_files'])!=regressions:raise ValueError('regression coverage differs')
 if not case_replays<=set(c['replay_files']):raise ValueError('case Replay coverage differs')
 if not (root/c['interface_file']).is_file():raise ValueError('interface example is missing')
 return {'library_modules':len(modules),'aggregate_project_modules':len(aggregate),
         'unaggregated_modules':len(uncovered),'smoke_files':len(smokes),
         'regression_files':len(regressions),'replay_files':len(c['replay_files']),
         'historical_replays_preserved_without_rerun':len(c['historical_replays_not_rerun']['files'])}

def axiom_audit(text,expected=()):
 entries=[(name,[v.strip() for v in body.split(',') if v.strip()])
          for name,body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)]
 entries += [(name,[]) for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
 invalid=[{'name':name,'axioms':axioms} for name,axioms in entries if not set(axioms)<=STANDARD_AXIOMS]
 unused=[name for name,_ in entries];missing=[]
 for name in expected:
  found=next((i for i,value in enumerate(unused) if value==name or value.endswith('.'+name)),None)
  if found is None:missing.append(name)
  else:unused.pop(found)
 malformed=(text.count('depends on axioms:')!=sum(1 for _ in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S))
            or text.count('does not depend on any axioms')!=len(re.findall(r"'([^']+)' does not depend on any axioms",text)))
 prohibited='sorryAx' in text or "declaration uses 'sorry'" in text
 return {'passed':not(invalid or missing or malformed or prohibited),'printed_declarations':len(entries),
         'expected_declarations':len(expected),'missing':missing,'nonstandard_axioms':invalid,
         'malformed_axiom_output':malformed,'sorry_found':prohibited}

def command_axiom_audit(root,argv,text):
 if argv[:2]!=['lake','build'] and argv[:3]!=['lake','env','lean']:return None
 expected=[]
 if argv[:3]==['lake','env','lean']:
  path=Path(argv[3]);path=path if path.is_absolute() else root/path
  expected=re.findall(r'^\s*#print\s+axioms\s+(\S+)',path.read_text(),re.M)
 return axiom_audit(text,expected)

def plan(mode,output,python):
 c=json.loads((ROOT/'scripts/verification.json').read_text());validate_checklist(ROOT,c);consumer=[python,str(ROOT/'tools/replay_pg_certificate.py')];case=ROOT/'data/cases/pg/two-step-reuse';p=[]
 def add(label,argv,limit=900):p.append({'label':label,'argv':argv,'timeout_seconds':limit})
 if mode=='quick':
  add('core',['lake','build',c['core']],1800)
  add('consumer_python',[python,str(ROOT/'scripts/test_python.py'),'--pattern','test_pg_certificate_consumer.py','-v'])
  add('interface_smoke',['lake','env','lean',c['interface_file']])
  add('pg2_verify',consumer+['verify','--source-root',str(ROOT),'--input',str(case/'capture.json'),'--candidate',str(case/'selected_exact.json'),'--output',str(output/'pg2-verify'),'--namespace','LeanPEP.Imported.Public.PG2','--timeout','900'],960)
  add('cleanup_dry_run',[python,str(ROOT/'scripts/clean.py')])
 elif mode=='tightness':
  for alg in ['PG','GD']:add('build_'+alg.lower()+'_tightness',['lake','build','LeanPEP.ActualFunction.'+alg+'OneCapturedTightness'],1800)
  for f in c['regression_files']:add(Path(f).stem,['lake','env','lean',f])
 else:
  add('python_full',[python,str(ROOT/'scripts/test_python.py'),'--inventory-json',str(output/'test-ids.json'),'-v'],1800)
  add('generated',[python,str(ROOT/'scripts/check_generated.py'),'--output',str(output/'generation')],900)
  add('core',['lake','build',c['core']],1800)
  add('prerequisites',['lake','build',*c['prerequisites']],1800)
  for m in c['sequential_regressions']:add('build_'+m.split('.')[-1],['lake','build',m],1200)
  add('aggregate',['lake','build',c['aggregate']],1800)
  for m in c['unaggregated_modules']:add('build_'+m.split('.')[-1],['lake','build',m],1200)
  for category in ['smoke_files','regression_files','replay_files']:
   for i,f in enumerate(c[category]):add(category+'_'+str(i)+'_'+Path(f).stem,['lake','env','lean',f],1200)
  add('interface_smoke',['lake','env','lean',c['interface_file']])
  add('pg2_recover',consumer+['recover','--source-root',str(ROOT),'--input',str(case/'capture.json'),'--output',str(output/'pg2-recover'),'--namespace','LeanPEP.Imported.Public.PG2','--timeout','900'],1020)
  add('cleanup_dry_run',[python,str(ROOT/'scripts/clean.py')])
 return p

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('mode',choices=['quick','full','tightness']);ap.add_argument('--output',type=Path);ap.add_argument('--list',action='store_true');ap.add_argument('--python',default=sys.executable);a=ap.parse_args()
 out=(a.output or Path('/tmp/lean-pep-checks-example')).resolve();p=plan(a.mode,out,a.python);coverage=validate_checklist(ROOT,json.loads((ROOT/'scripts/verification.json').read_text()))
 if a.list:print(json.dumps(p,indent=2));return 0
 if a.output is None:ap.error('--output required for execution')
 if out==ROOT or ROOT in out.parents or out.exists():ap.error('output must be fresh and outside the source')
 out.mkdir(parents=True);(out/'plan.json').write_text(json.dumps(p,indent=2)+'\n');env=os.environ.copy()
 for key in ['LEAN_PATH','LEAN_SRC_PATH','PYTHONPATH']:env.pop(key,None)
 env['PYTHONDONTWRITEBYTECODE']='1';records=[];status='passed'
 for index,item in enumerate(p):
  label=f'{index:03d}_{item["label"]}';log=out/(label+'.log');start=time.monotonic()
  timed_out=False
  with log.open('w') as stream:
   child=subprocess.Popen(item['argv'],cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
   try:code=child.wait(timeout=item['timeout_seconds'])
   except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait();code=124;timed_out=True
  audit=command_axiom_audit(ROOT,item['argv'],log.read_text())
  rec={**item,'cwd':str(ROOT),'exit':code,'timed_out':timed_out,'signal_number':-code if code<0 else None,'wall_seconds':time.monotonic()-start,'log':log.name,'axiom_audit':audit,'environment':{'LEAN_PATH':'unset','PYTHONPATH':'unset','LEAN_SRC_PATH':'unset','PYTHONDONTWRITEBYTECODE':'1'}};records.append(rec);(out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');print(label,code,flush=True)
  if code:status='resource_limit' if timed_out else 'signal_terminated' if code<0 else 'failed';break
  if audit is not None and not audit['passed']:status='axiom_audit_failed';break
 if status=='passed' and a.mode=='full':
  candidate=out/'pg2-recover/selected_exact.json';expected=ROOT/'data/cases/pg/two-step-reuse/selected_exact.json'
  if candidate.read_bytes()!=expected.read_bytes():status='selected_data_mismatch'
 (out/'result.json').write_text(json.dumps({'status':status,'mode':a.mode,'coverage':coverage,'completed_commands':len(records),'planned_commands':len(p),'live_capture_performed':False,'standard_axioms_checked_by_consumer':any(r['label'] in ['pg2_verify','pg2_recover'] and r['exit']==0 for r in records),'direct_axiom_audits':[{'label':r['label'],**r['axiom_audit']} for r in records if r['axiom_audit'] is not None],'selected_byte_comparison':status=='passed' if a.mode=='full' else 'not applicable'},indent=2)+'\n')
 return 0 if status=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
