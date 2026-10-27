#!/usr/bin/env python3
"""Install locked external dependencies and build the certificate Core from this source tree.

Default: official upstream Git plus matching Mathlib binary cache. --cache delegates
pin/clean validation and copying to the existing consumer. Neither path copies a
LeanPEP object. Outputs and command logs must be outside the source tree.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,signal,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,value):p.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def clean_environment():
    env=os.environ.copy()
    for name in ['LEAN_PATH','PYTHONPATH','LEAN_SRC_PATH','LAKE_HOME','ELAN_TOOLCHAIN']:env.pop(name,None)
    env.update(PYTHONDONTWRITEBYTECODE='1',GIT_TERMINAL_PROMPT='0')
    return env

def validate_manifest(root):
    root=root.resolve();manifest=root/'SOURCE_MANIFEST.json'
    if manifest.is_symlink():raise ValueError('source manifest must be a regular file')
    obj=json.loads(manifest.read_text());files=obj['files']
    if not re.fullmatch(r'sha256:[a-f0-9]{64}',obj['source_id']):raise ValueError('invalid source identity')
    canonical=json.dumps({'files':files},sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()
    if obj['source_id']!='sha256:'+hashlib.sha256(canonical).hexdigest():raise ValueError('source identity digest mismatch')
    if files!=sorted(files,key=lambda x:x['path']):raise ValueError('source manifest paths must be sorted POSIX strings')
    seen=set()
    for entry in files:
        rel=Path(entry['path'])
        if rel.is_absolute() or '..' in rel.parts or rel.as_posix() in seen:raise ValueError('unsafe or duplicate manifest path')
        seen.add(rel.as_posix());p=root/rel
        if any((root/Path(*rel.parts[:i])).is_symlink() for i in range(1,len(rel.parts)+1)) or not p.is_file():raise ValueError('nonregular source input: '+rel.as_posix())
        if p.stat().st_size!=entry['bytes'] or digest(p)!=entry['sha256']:raise ValueError('source manifest hash mismatch: '+rel.as_posix())
    required={'lake-manifest.json','lean-toolchain','lakefile.lean','docs/pg-core-content-review.json','tools/replay_pg_certificate.py','scripts/setup.py'}
    if not required<=seen:raise ValueError('manifest omits required setup/lock/Core guard input')
    return obj

def locked_packages(root):
    obj=json.loads((root/'lake-manifest.json').read_text());packages=obj['packages']
    if len(packages)!=9 or len({x['name'] for x in packages})!=9:raise ValueError('expected nine distinct locked dependency packages')
    for pkg in packages:
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*',pkg['name']) or pkg.get('type')!='git' or not re.fullmatch(r'[a-f0-9]{40}',pkg['rev']):raise ValueError('invalid locked Git package')
        if not pkg['url'].startswith('https://github.com/'):raise ValueError('expected official GitHub dependency URL')
    return packages

def mathlib_imports(root):
    """Direct Mathlib imports for the full maintained library and executable cases.

    Mathlib cache resolves their transitive dependency closure itself. Historical
    data/paper Replays and JSON fixtures are provenance, not extra build roots.
    """
    inputs=[root/'LeanPEP.lean']
    for name in ['LeanPEP','tests/lean','data/cases','examples']:
        base=root/name
        if base.exists():inputs.extend(base.rglob('*.lean'))
    imports=set()
    for p in inputs:
        if not p.is_file():continue
        for line in re.findall(r'^\s*import ([^\n]+)',p.read_text(),re.M):
            for dep in line.split():
                if dep=='Mathlib' or dep.startswith('Mathlib.'):
                    if not re.fullmatch(r"[A-Za-z_][\w.']*",dep):raise ValueError('unsupported import syntax: '+str(p))
                    imports.add(dep)
    if not imports:raise ValueError('no Mathlib imports found in maintained source')
    return sorted(imports)

def require_clean_project(root):
    if (root/'.lake/build').exists() or (root/'.lake/build').is_symlink():raise ValueError('initial project .lake/build must be absent')
    for base,dirs,files in os.walk(root,followlinks=False):
        dirs[:]=[d for d in dirs if d not in ['.git','.lake','.venv-pepit'] and not (Path(base)/d).is_symlink()]
        if any(Path(f).suffix in ['.olean','.ilean'] for f in files):raise ValueError('initial source tree contains project Lean objects')

def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True,help='new external directory for installation receipts and optional fresh toolchain/cache')
    ap.add_argument('--cache',type=Path,help='existing clean cache containing only the nine locked external package directories')
    ap.add_argument('--dependencies-only',action='store_true',help='prepare dependencies and matching cache; do not build LeanPEP Core')
    ap.add_argument('--elan',default='elan',help='existing elan manager executable')
    ap.add_argument('--fresh-toolchain',action='store_true',help='download the locked toolchain under --output instead of reusing a system installation')
    a=ap.parse_args(argv);root=ROOT;out=a.output.resolve()
    if out==root or root in out.parents:raise ValueError('output must be outside source root')
    if out.exists():raise ValueError('output must not exist')
    out.mkdir(parents=True);env=clean_environment();records=[]
    report=dict(status='not_verified',source_root=str(root),source_id=None,dependencies_only=a.dependencies_only,old_project_objects_used=False,dependency_mode='validated locked cache' if a.cache else 'official upstream Git and matching binary cache',dependency_source_cold_build=False)
    def run(label,args,cwd=root,limit=1200):
        log=out/(f'{len(records)+1:02}_'+label+'.log');start=time.monotonic()
        with log.open('w') as f:
            p=subprocess.Popen([str(x) for x in args],cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:rc=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait();rc=124
        records.append(dict(label=label,cwd=str(cwd),argv=[str(x) for x in args],exit=rc,wall_seconds=time.monotonic()-start,log=log.name))
        write(out/'commands.json',records);print(label,rc,flush=True)
        if rc:raise RuntimeError(label+': exit '+str(rc)+'; see '+log.name)
        return log
    try:
        manifest=validate_manifest(root);report['source_id']=manifest['source_id'];packages=locked_packages(root);require_clean_project(root)
        lock_sha=digest(root/'lake-manifest.json');toolchain=(root/'lean-toolchain').read_text().strip()
        if not re.fullmatch(r'leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+',toolchain):raise ValueError('unsupported locked toolchain spelling')
        env['ELAN_TOOLCHAIN']=toolchain
        if a.fresh_toolchain:
            env.update(ELAN_HOME=str(out/'elan'),XDG_CACHE_HOME=str(out/'xdg-cache'),MATHLIB_CACHE_DIR=str(out/'mathlib-cache'))
        # Ask elan for the exact compiler, installing only when that locked toolchain is absent.
        probe=subprocess.run([a.elan,'which','lean'],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        write(out/'toolchain-probe.json',dict(argv=[a.elan,'which','lean'],exit=probe.returncode,stdout=probe.stdout,stderr=probe.stderr))
        if probe.returncode:
            run('install_locked_toolchain',[a.elan,'toolchain','install',toolchain],limit=900)
            probe=subprocess.run([a.elan,'which','lean'],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if probe.returncode:raise RuntimeError('locked toolchain lookup failed: '+probe.stderr.strip())
        lean=Path(probe.stdout.strip());lake=lean.with_name('lake')
        if not lean.is_file() or not lake.is_file():raise RuntimeError('locked Lean/Lake executables missing')
        env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
        run('lean_version',[lean,'--version']);run('lake_help',[lake,'--help'])
        consumer=root/'tools/replay_pg_certificate.py'
        if a.cache:
            run('consumer_dependencies',[sys.executable,consumer,'dependencies','--source-root',root,'--cache',a.cache.resolve(),'--output',out/'dependencies'])
        else:
            pkgs=root/'.lake/packages'
            if pkgs.exists():raise ValueError('dependency destination already exists; use a clean source directory')
            pkgs.mkdir(parents=True);dep=[]
            for p in packages:
                folder=pkgs/p['name'];folder.mkdir()
                for label,args in [('init',['git','init',folder]),('remote',['git','-C',folder,'remote','add','origin',p['url']]),('fetch',['git','-C',folder,'fetch','--depth','1','origin',p['rev']]),('checkout',['git','-C',folder,'checkout','--detach','FETCH_HEAD'])]:run(p['name']+'_'+label,args)
                revlog=run(p['name']+'_revision',['git','-C',folder,'rev-parse','HEAD'])
                dirtylog=run(p['name']+'_clean',['git','-C',folder,'status','--porcelain'])
                if revlog.read_text().strip()!=p['rev'] or dirtylog.read_text().strip():raise ValueError('dependency revision/clean mismatch: '+p['name'])
                dep.append(dict(name=p['name'],url=p['url'],revision=p['rev'],clean=True))
            write(out/'dependencies.json',dep)
            help_log=run('official_cache_help',[lake,'exe','cache','--help'])
            if 'get [ARGS]' not in help_log.read_text():raise RuntimeError('cache help did not confirm expected get arguments')
            imports=mathlib_imports(root)
            write(out/'cache-scope.json',dict(mathlib_import_roots=imports,scope='direct Mathlib imports of full LeanPEP library, smoke/regression tests and maintained examples/cases; cache tool resolves transitive dependencies',dependency_source_cold_build=False))
            run('official_cache_get',[lake,'exe','cache','get',*imports],limit=1800)
        if digest(root/'lake-manifest.json')!=lock_sha:raise ValueError('lockfile changed')
        if not a.dependencies_only:run('consumer_core_build',[sys.executable,consumer,'build','--source-root',root,'--output',out/'core-build','--timeout','1800'],limit=1830)
        validate_manifest(root)
        report.update(status='dependencies_ready' if a.dependencies_only else 'core_built',toolchain=toolchain,lock_sha256=lock_sha)
        return 0
    except (ValueError,OSError,RuntimeError,KeyError) as exc:
        report['first_error']=str(exc);print(str(exc),file=sys.stderr);return 1
    finally:write(out/'result.json',report)

if __name__=='__main__':
    try:raise SystemExit(main())
    except (ValueError,OSError) as exc:print(str(exc),file=sys.stderr);raise SystemExit(1)
