#!/usr/bin/env python3
"""Start Here: fetch pinned public dependencies, build Core, consume a supplied PG2 input."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time,zipfile,signal,datetime
ZIP_SHA='e2fa8b8d6f85fa8e8cfc07daec3447e0adebb7f2732a69b1441185584fcab0b3'
TOOLCHAIN='leanprover/lean4:v4.31.0'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,o):p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def unpack(zpath,dst):
 with zipfile.ZipFile(zpath) as z:
  for item in z.infolist():
   q=Path(item.filename)
   if q.is_absolute() or '..' in q.parts or (item.external_attr>>16)&0o170000==0o120000:raise ValueError('unsafe ZIP path')
  z.extractall(dst)
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source-zip',type=Path,required=True);ap.add_argument('--input',type=Path,required=True)
 ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--destination',type=Path,required=True)
 ap.add_argument('--phase',choices=['prepare','verify','all'],default='all')
 ap.add_argument('--elan',default='elan',help='existing elan manager executable; no existing toolchain/cache is used')
 a=ap.parse_args();dest=a.destination.resolve();dest.mkdir(parents=True,exist_ok=True);logs=dest/'install-logs';logs.mkdir(exist_ok=True)
 root=dest/'source';entryhash=sha(Path(__file__))
 env=os.environ.copy()
 for name in ['LEAN_PATH','PYTHONPATH','LEAN_SRC_PATH','LAKE_HOME']:env.pop(name,None)
 env.update(ELAN_HOME=str(dest/'elan'),XDG_CACHE_HOME=str(dest/'xdg-cache'),MATHLIB_CACHE_DIR=str(dest/'mathlib-downloads'),PYTHONDONTWRITEBYTECODE='1',GIT_TERMINAL_PROMPT='0')
 oldpath=env.get('PATH','');binpath=dest/'elan/toolchains/leanprover--lean4---v4.31.0/bin'
 # Fully qualified fresh tools precede system prereqs. Never fall back to old Lean/Lake.
 env['PATH']=str(binpath)+':'+oldpath
 records=json.loads((logs/'commands.json').read_text()) if (logs/'commands.json').exists() else []
 def run(label,argv,cwd,limit=600):
  num=len(records)+1;log=logs/f'{num:02}_{label}.log';t=time.monotonic();at=datetime.datetime.now(datetime.timezone.utc).isoformat()
  with log.open('w') as f:
   proc=subprocess.Popen(argv,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
   try:rc=proc.wait(timeout=limit)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=124
  record=dict(label=label,argv=argv,cwd=str(cwd),exit=rc,wall_seconds=time.monotonic()-t,started_at_utc=at,log=log.name)
  records.append(record);write(logs/'commands.json',records);print(label,rc,flush=True)
  if rc:raise RuntimeError(f'{label}: exit {rc}; first direct error is in {log.name}')
  return log
 report=dict(status='started',source_zip_sha256=sha(a.source_zip),entry_sha256=entryhash,
             source_id='sha256:e43a0018cd7dd8d202361abcea8fcbbda1db7981bf25ec5e36c317116b1f429c',
             old_author_cache_used=False,environment={k:env[k] for k in ['ELAN_HOME','XDG_CACHE_HOME','MATHLIB_CACHE_DIR']},
             cache_scope='official matching-revision binary dependencies; no dependency-source cold-build claim')
 try:
  if sha(a.source_zip)!=ZIP_SHA:raise ValueError('source archive identity mismatch')
  if a.phase in ['prepare','all']:
   if root.exists():raise ValueError('fresh source destination required; use verify only after prepared')
   root.mkdir();unpack(a.source_zip,root)
   if (root/'.git').exists() or (root/'.lake').exists():raise ValueError('source archive must not contain project/dependency build state')
   if not (binpath/'lean').exists():run('elan_toolchain_install',[a.elan,'toolchain','install',TOOLCHAIN],dest,600)
   else:print('using already downloaded fresh-destination toolchain',flush=True)
   if not (binpath/'lake').is_file():raise RuntimeError('fresh Lake missing')
   run('fresh_lean_version',[str(binpath/'lean'),'--version'],dest)
   run('fresh_lake_help',[str(binpath/'lake'),'--help'],dest)
   original_manifest=sha(root/'lake-manifest.json');packages=json.loads((root/'lake-manifest.json').read_text())['packages']
   pkgs=root/'.lake/packages';pkgs.mkdir(parents=True)
   dep=[]
   for p in packages:
    folder=pkgs/p['name'];folder.mkdir()
    run(p['name']+'_git_init',['git','init',str(folder)],dest)
    run(p['name']+'_remote',['git','-C',str(folder),'remote','add','origin',p['url']],dest)
    run(p['name']+'_fetch',['git','-C',str(folder),'fetch','--depth','1','origin',p['rev']],dest,300)
    run(p['name']+'_checkout',['git','-C',str(folder),'checkout','--detach','FETCH_HEAD'],dest)
    rev=subprocess.check_output(['git','-C',str(folder),'rev-parse','HEAD'],text=True).strip()
    dirty=subprocess.check_output(['git','-C',str(folder),'status','--porcelain'],text=True)
    if rev!=p['rev'] or dirty:raise RuntimeError('dependency revision/clean mismatch '+p['name'])
    dep.append(dict(name=p['name'],url=p['url'],revision=rev,clean=True,source='official upstream Git fetch'))
   if sha(root/'lake-manifest.json')!=original_manifest:raise RuntimeError('lockfile changed')
   write(logs/'dependencies.json',dep);write(logs/'prepared.json',dict(source_manifest_sha256=original_manifest,toolchain=TOOLCHAIN))
  if a.phase in ['verify','all']:
   prepared=json.loads((logs/'prepared.json').read_text())
   if sha(root/'lake-manifest.json')!=prepared['source_manifest_sha256']:raise RuntimeError('lockfile changed')
   if (root/'.lake/build').exists():raise RuntimeError('initial project build output must be absent')
   help_log=run('official_cache_help',[str(binpath/'lake'),'exe','cache','--help'],root,600)
   if 'get [ARGS]' not in help_log.read_text():raise RuntimeError('cache CLI arguments not verified; inspect help')
   review=json.loads((root/'docs/pg-core-content-review.json').read_text())
   mathimports=sorted({i for v in review['modules'].values() for i in v['imports'] if i.startswith('Mathlib')})
   run('official_cache_get',[str(binpath/'lake'),'exe','cache','get',*mathimports],root,1200)
   # Cache tooling can create package-configuration metadata, but no old LeanPEP outputs were supplied.
   write(logs/'before_core_build.json',dict(old_project_output_supplied=False,mathlib_import_roots=mathimports))
   consumer=str(root/'tools/replay_pg_certificate.py')
   run('consumer_help',[sys.executable,consumer,'--help'],root)
   run('consumer_core_build',[sys.executable,consumer,'build','--source-root',str(root),'--output',str(dest/'core-build'),'--timeout','1800'],root,1830)
   run('consumer_verify',[sys.executable,consumer,'verify','--source-root',str(root),'--input',str(a.input.resolve()),'--candidate',str(a.candidate.resolve()),'--output',str(dest/'verify'),'--namespace','LeanPEP.Imported.Refine001.FreshInstall','--timeout','900'],root,960)
   result=json.loads((dest/'verify/result.json').read_text())
   if not result.get('actual_upper_verified'):raise RuntimeError('actual theorem not verified')
   if sha(root/'lake-manifest.json')!=prepared['source_manifest_sha256']:raise RuntimeError('lockfile changed')
   report.update(actual_upper_verified=True,bound=result.get('bound'),namespace='LeanPEP.Imported.Refine001.FreshInstall')
  report.update(status='prepared' if a.phase=='prepare' else 'verified')
 except Exception as exc:report.update(status='not_verified',first_error=str(exc));print(str(exc),file=sys.stderr);return 1
 finally:write(logs/('result-'+a.phase+'.json'),report)
 return 0
if __name__=='__main__':raise SystemExit(main())

