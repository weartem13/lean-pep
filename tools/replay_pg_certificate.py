#!/usr/bin/env python3
"""Relocatable PG2 certificate consumer. Recovery needs Python's standard library only.
Numerical capture is separate. Existing hash-locked archive tools are unchanged.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap
import import_proximal_gradient_sparse as sparse
import replay_structured_pg_two as strategy

CORE='LeanPEP.ActualFunction.ProximalGradientCaptureAuditCore'
RULE='pg2_source_affine_grid_v1_64_trials'
REVIEW='docs/pg-core-content-review.json'

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def require(ok,message):
    if not ok:raise ValueError(message)

def fresh_output(root,out):
    root=root.resolve();out=out.resolve()
    require(out!=root and root not in out.parents,'output must be outside source root')
    require(not out.exists(),'output must not already exist')
    out.mkdir(parents=True)
    return root,out

def peak_rss(children=False):
    try:
        import resource
        value=resource.getrusage(resource.RUSAGE_CHILDREN if children else resource.RUSAGE_SELF).ru_maxrss
        return value if sys.platform=='darwin' else value*1024 if sys.platform.startswith('linux') else None
    except (ImportError, OSError, ValueError):
        return None

def run_command(root,out,name,argv,timeout=900):
    env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('PYTHONPATH',None);env['PYTHONDONTWRITEBYTECODE']='1'
    start=time.monotonic()
    with (out/(name+'.log')).open('w') as f:
        try: rc=subprocess.run(argv,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout).returncode
        except subprocess.TimeoutExpired:rc=124
    record=dict(cwd=str(root),argv=argv,exit=rc,wall_seconds=time.monotonic()-start,log=name+'.log',peak_rss_bytes=peak_rss(True),resource_scope='getrusage CHILDREN high-water mark in this consumer process, bytes; not process-tree sum; descendant inclusion unverified',timeout_seconds=timeout,LEAN_PATH='unset')
    p=out/'commands.json';records=json.loads(p.read_text()) if p.exists() else [];records.append(record);write(p,records)
    return rc

def dependency_graph(root):
    """Read project imports; missing project sources fail closed. Not a Lean parser."""
    graph={}
    def visit(m):
        if m!='LeanPEP' and not m.startswith('LeanPEP.'):return
        if m in graph:return
        p=root/(m.replace('.','/')+'.lean')
        require(p.is_file(),'missing LeanPEP source: '+m)
        graph[m]=[dep for line in re.findall(r'^\s*import ([^\n]+)',p.read_text(),re.M) for dep in line.split()]
        require(all(re.fullmatch(r"[A-Za-z_][\w.']*",d) for d in graph[m]),'unreviewed import syntax: '+m)
        for dep in graph[m]:visit(dep)
    visit(CORE)
    return graph

def closure(root):
    graph=dependency_graph(root)
    review=json.loads((root/REVIEW).read_text())
    require(review['root']==CORE and review['schema']=='leanpep-content-review-v1','invalid content review')
    approved=review['modules']
    unknown=sorted(set(graph)-set(approved))
    require(not unknown,'unreviewed project modules: '+', '.join(unknown))
    for m,deps in graph.items():
        item=approved[m]
        require(item['classification']=='generic' and bool(item['rationale']),'non-generic/unreviewed content: '+m)
        require(digest(root/(m.replace('.','/')+'.lean'))==item['sha256'],'content review stale: '+m)
        require(deps==item['imports'],'dependency review stale: '+m)
    require(set(graph)==set(approved),'content review closure differs; review required')
    return graph

def read_capture(path,expected=None):
    if expected:require(digest(path)==expected,'input integrity hash mismatch')
    c=cap.convert(gram.load_json(path),2);strategy.validate_source(c)
    return c

def render(c,candidate,namespace):
    text=strategy.render_replay(c,candidate,namespace)
    require(text.startswith('import LeanPEP\n'),'unexpected legacy renderer header')
    return text.replace('import LeanPEP\n','import '+CORE+'\n',1)+f'\n#print axioms LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic\n'

def dependencies(root,cache,out):
    target=root/'.lake/packages';require(not target.exists(),'dependency destination already exists')
    records=[]
    for pkg in json.loads((root/'lake-manifest.json').read_text())['packages']:
        p=cache/pkg['name'];rev=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
        require(rev==pkg['rev'],'dependency pin mismatch: '+pkg['name'])
        dirty=subprocess.check_output(['git','-C',str(p),'status','--porcelain'],text=True);require(not dirty,'dirty dependency: '+pkg['name'])
        records.append(dict(name=pkg['name'],revision=rev))
    require(set(p.name for p in cache.iterdir())=={p['name'] for p in records},'cache must contain only locked external packages')
    target.mkdir(parents=True)
    for pkg in records:
        src=cache/pkg['name'];dst=target/pkg['name']
        if sys.platform=='darwin':subprocess.run(['cp','-cR',str(src),str(dst)],check=True)
        else:shutil.copytree(src,dst,symlinks=True)
    for p in target.rglob('*'):
        if p.is_symlink():require(p.resolve().is_relative_to(target.resolve()),'external dependency symlink')
    write(out/'dependencies.json',records)

def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('mode',choices=['dependencies','build','recover','verify'])
    ap.add_argument('--source-root',type=Path,required=True);ap.add_argument('--input',type=Path);ap.add_argument('--candidate',type=Path);ap.add_argument('--cache',type=Path)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--namespace',default='LeanPEP.Imported.Consumer.PG2');ap.add_argument('--expected-sha256');ap.add_argument('--timeout',type=int,default=900)
    a=ap.parse_args(argv);root=a.source_root.resolve();out=a.output.resolve()
    require((root/'tools/replay_pg_certificate.py').resolve()==Path(__file__).resolve(),'execute the consumer from the selected source package')
    root,out=fresh_output(root,out);report=dict(mode=a.mode,status='started',rule=RULE,live_capture_performed=False,selected_endpoint=None,actual_upper_verified=False,pure_closure_status='pending',execution_status='not_run')
    original={p.resolve():digest(p) for p in [a.input,a.candidate] if p}
    try:
        write(out/'import_graph.json',closure(root))
        report['pure_closure_status']='passed_content_review'
        if a.mode=='dependencies':
            require(a.cache is not None,'--cache required');dependencies(root,a.cache.resolve(),out)
        elif a.mode=='build':
            rc=run_command(root,out,'core_build',['lake','build',CORE],a.timeout);require(rc==0,'core build failed or limit')
        else:
            require(a.input is not None,'--input capture required');c=read_capture(a.input,a.expected_sha256)
            start=time.monotonic()
            if a.mode=='recover':candidate,audit,generation=strategy.build_candidate(c)
            else:
                require(a.candidate is not None,'--candidate required in verify mode')
                candidate=sparse.parse_artifact(gram.load_json(a.candidate),2);audit=strategy.audit_candidate(c,candidate);generation=dict(mode='check supplied exact candidate; no solver')
            write(out/'generation.json',dict(generation,wall_seconds=time.monotonic()-start,peak_rss_bytes=peak_rss(),resource_scope='getrusage SELF process high-water mark including imports, before Lean',consumer_rule=RULE))
            write(out/'direct_audit.json',audit);require(audit['candidate_diagnostic_accepted'],'candidate rejected by original diagnostics')
            write(out/'candidate_exact.json',sparse.artifact_tree(candidate));(out/'Replay.lean').write_text(render(c,candidate,a.namespace))
            write(out/'input_identity.json',dict(capture_sha256=digest(a.input),candidate_sha256=digest(out/'candidate_exact.json'),replay_sha256=digest(out/'Replay.lean')))
            rc=run_command(root,out,'replay',['lake','env','lean',str(out/'Replay.lean')],a.timeout)
            require(rc==0,'Lean failed or limit')
            log=(out/'replay.log').read_text();require(strategy.pipeline.axiom_output_ok(log,a.namespace,True) and 'sorryAx' not in log,'axiom audit failed')
            shutil.copyfile(out/'candidate_exact.json',out/'selected_exact.json')
            report.update(selected_endpoint='structured',actual_upper_verified=True,bound=str(candidate.upper.bound),residual_recomputed=True)
        report.update(status='passed',execution_status='passed');return 0
    except Exception as exc:
        if report['pure_closure_status']=='pending':report['pure_closure_status']='failed_or_unreviewed'
        report.update(status='failed_or_limit',execution_status='failed_or_not_run',error=str(exc));print(str(exc),file=sys.stderr);return 1
    finally:
        report['inputs_unchanged']=all(digest(p)==h for p,h in original.items());write(out/'result.json',report)

if __name__=='__main__':
    try:raise SystemExit(main())
    except (ValueError,OSError) as exc:print('error: '+str(exc),file=sys.stderr);raise SystemExit(1)
