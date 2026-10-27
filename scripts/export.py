#!/usr/bin/env python3
"""Export a code/reproduction snapshot or a separate local paper ZIP, without Git history."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,zipfile
ROOT=Path(__file__).resolve().parents[1]
DIRECTORIES=['LeanPEP','tools','scripts','tests','examples','data','docs']
# These local manuscript/publication records are not code-distribution inputs.
# Retain them in the maintained tree; paper_archive is a separate explicit mode.
LOCAL_ONLY={'docs/publication.json','docs/release-notes-v0.1.0.md',
            'data/paper/validation/metadata-errata.json'}
FILES=['LeanPEP.lean','lakefile.lean','lake-manifest.json','lean-toolchain','README.md','.gitignore','requirements-pepit-capture.txt','requirements-test.txt','CITATION.cff','CHANGELOG.md','LICENSE']
# Preserve an actual project notice if one is supplied; do not synthesize one.
OPTIONAL_FILES=['NOTICE']
SKIP={'__pycache__','.pytest_cache','.DS_Store','.git','.lake'}
INTERMEDIATES={'.pyc','.olean','.ilean','.aux','.log','.out','.bbl','.blg','.fls','.toc','.vtc','.fdb_latexmk'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def regular_input(p):
 rel=p.relative_to(ROOT)
 if any((ROOT/Path(*rel.parts[:i])).is_symlink() for i in range(1,len(rel.parts)+1)):
  raise ValueError('export rejects symlink '+str(rel))
 if not p.is_file():raise ValueError('export input is not a regular file: '+str(rel))
 return {'path':rel.as_posix(),'bytes':p.stat().st_size,'sha256':digest(p)}
def inventory():
 out=[]
 for name in FILES+OPTIONAL_FILES+DIRECTORIES:
  base=ROOT/name
  if base.is_symlink():raise ValueError('export rejects symlink '+name)
  if not base.exists():
   if name in OPTIONAL_FILES:continue
   raise ValueError('missing export input '+name)
  if base.is_file():
   out.append(regular_input(base));continue
  for directory,dirs,files in os.walk(base,followlinks=False):
   parent=Path(directory);keep=[]
   for child in sorted(dirs):
    p=parent/child;rel=p.relative_to(ROOT)
    if p.is_symlink():raise ValueError('export rejects symlink '+str(rel))
    if child in SKIP or child.startswith('.venv'):continue
    if child.startswith('.'):raise ValueError('unreviewed hidden directory: '+str(rel))
    keep.append(child)
   dirs[:]=keep
   for child in sorted(files):
    p=parent/child;rel=p.relative_to(ROOT)
    if p.is_symlink():raise ValueError('export rejects symlink '+str(rel))
    if child in SKIP or rel.as_posix() in LOCAL_ONLY:continue
    if child.startswith('.'):raise ValueError('unreviewed hidden file: '+str(rel))
    # Historical data logs are evidence, not disposable build products.
    if rel.parts[0]!='data' and (p.suffix in INTERMEDIATES or child.endswith('.synctex.gz')):continue
    out.append(regular_input(p))
 return sorted(out,key=lambda x:x['path'])
def identity(files):return 'sha256:'+hashlib.sha256(json.dumps({'files':files},sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def fresh_destination(path):
 if path.is_symlink():raise ValueError('output must not be a symlink')
 out=path.resolve();root=ROOT.resolve()
 if out.exists() or out==root or root in out.parents:raise ValueError('output must be fresh and outside source')
 return out
def paper_inputs():
 """Follow the literal inputs in this manuscript; no general TeX evaluation."""
 found=set();active=set()
 def visit(name):
  rel=Path(name)
  if rel.is_absolute() or '..' in rel.parts or any(x.startswith('.') for x in rel.parts):
   raise ValueError('unsafe paper input: '+name)
  if rel.suffix!='.tex':raise ValueError('paper input must name a .tex file: '+name)
  if name in active:raise ValueError('cyclic paper input: '+name)
  if name in found:return
  p=ROOT/'paper'/rel;regular_input(p);active.add(name)
  text=re.sub(r'(?<!\\)%[^\n]*','',p.read_text())
  if r'\includegraphics' in text:raise ValueError('review new graphic assets before extending paper packaging')
  for child in re.findall(r'\\(?:input|include)\{([^}]+)\}',text):visit(child)
  active.remove(name);found.add(name)
 visit('main.tex')
 # These reviewed local styles are required by the LIPIcs preprint configuration.
 # The class logo is not used with \hideLIPIcs; confirm this in the build recorder.
 main_text=re.sub(r'(?<!\\)%[^\n]*','',(ROOT/'paper/main.tex').read_text())
 for pattern,name in [
   (r'\\documentclass(?:\[[^\]]*\])?\{lipics-v2021\}','lipics-v2021.cls'),
   (r'\\bibliographystyle\{unsrturl\}','unsrturl.bst')]:
  if re.search(pattern,main_text):
   regular_input(ROOT/'paper'/name);found.add(name)
 for name in ['references.bib','LICENSE','README.md']:
  regular_input(ROOT/'paper'/name);found.add(name)
 return sorted(found)
def paper_archive(out,bbl):
 if bbl.is_symlink() or not bbl.is_file() or not bbl.stat().st_size:raise ValueError('--bbl must be a nonempty regular file from the final BibTeX build')
 names=paper_inputs()
 out.parent.mkdir(parents=True,exist_ok=True)
 with zipfile.ZipFile(out,'x',compression=zipfile.ZIP_DEFLATED) as archive:
  for name in names:archive.write(ROOT/'paper'/name,name)
  archive.write(bbl,'main.bbl')
 print(json.dumps({'output':str(out),'sha256':digest(out),'files':names+['main.bbl'],'bbl_sha256':digest(bbl)},indent=2))
def main(argv=None):
 ap=argparse.ArgumentParser(description=__doc__)
 mode=ap.add_mutually_exclusive_group(required=True)
 mode.add_argument('--output',type=Path,help='new external directory for code, tests, documentation and reproduction evidence (no manuscript)')
 mode.add_argument('--manifest-only',action='store_true')
 mode.add_argument('--paper-output',type=Path,help='new external arXiv ZIP containing manuscript inputs, main.bbl, paper LICENSE and README')
 ap.add_argument('--bbl',type=Path,help='matching main.bbl generated from the final manuscript; required with --paper-output')
 a=ap.parse_args(argv)
 if bool(a.paper_output)!=bool(a.bbl):ap.error('--bbl is required only with --paper-output')
 # Validate destinations and protected files before writing any manifest or output.
 out=fresh_destination(a.paper_output or a.output) if not a.manifest_only else None
 if a.paper_output:paper_archive(out,a.bbl);return
 target=ROOT/'SOURCE_MANIFEST.json'
 if target.is_symlink() or (target.exists() and not target.is_file()):raise ValueError('source manifest must be a regular file')
 files=inventory();source=files
 manifest={'source_id':identity(source),'files':source,'scope':'maintained code, required case/fixture data, retained experiment and execution evidence, tests, scripts, locks, requirements and documentation; manuscript and local publication records excluded; historical executions retain their original source identities'}
 if a.manifest_only:
  target.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print(manifest['source_id']);return
 out.mkdir(parents=True)
 for f in files:
  dst=out/f['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/f['path'],dst)
  if digest(dst)!=f['sha256']:raise ValueError('input changed during export: '+f['path'])
 target.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
 shutil.copy2(target,out/'SOURCE_MANIFEST.json')
 public={'public_id':identity(files),'source_id':manifest['source_id'],'files':files};(out/'PUBLIC_MANIFEST.json').write_text(json.dumps(public,indent=2,sort_keys=True)+'\n');print(json.dumps({'source_id':manifest['source_id'],'public_id':public['public_id'],'output':str(out),'files':len(files)},indent=2))
if __name__=='__main__':
 try:main()
 except (ValueError,OSError) as exc:raise SystemExit(str(exc))
