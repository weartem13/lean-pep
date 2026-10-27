#!/usr/bin/env python3
"""List approved reproducible outputs; remove them only with --apply.

Never cleans dependency packages, virtual environments, retained data, original
execution evidence, raw/selected inputs, or Lean source. Symlinks fail closed.
"""
from pathlib import Path
import argparse,json,os,shutil
ROOT=Path(__file__).resolve().parents[1]
PROTECTED_NAMES={'capture.json','selected_exact.json','selected_primal.json','raw_exact.json','primal_observation.json'}

def checked_tree(root,path,kind):
    root=root.resolve();rel=path.relative_to(root)
    if any((root/Path(*rel.parts[:i])).is_symlink() for i in range(1,len(rel.parts)+1)):raise ValueError('refusing symlink: '+rel.as_posix())
    for base,dirs,files in os.walk(path,followlinks=False):
        for n in dirs+files:
            p=Path(base)/n
            if p.is_symlink():raise ValueError('refusing symlink: '+p.relative_to(root).as_posix())
            if p.is_file():
                if p.name in PROTECTED_NAMES or (p.suffix.lower()=='.json' and p.stem.lower().startswith(('raw','selected','capture','primal'))) or p.suffix in ['.lean','.tex','.bib']:raise ValueError('protected input in cleanup target: '+p.relative_to(root).as_posix())
                if kind=='python_bytecode' and p.suffix not in ['.pyc','.pyo']:raise ValueError('unexpected file in bytecode directory: '+p.relative_to(root).as_posix())
    return dict(path=rel.as_posix(),category=kind)

def plan(root):
    root=root.resolve();result=[]
    for rel,kind in [('.lake/build','project_lean_objects'),('paper/build','tex_intermediates')]:
        p=root/rel
        if p.exists() or p.is_symlink():result.append(checked_tree(root,p,kind))
    # Limit Python cleanup to active implementation/test/entry directories.
    for name in ['tools','tests','scripts']:
        start=root/name
        if start.is_symlink():raise ValueError('refusing symlink: '+name)
        if not start.is_dir():continue
        for base,dirs,_ in os.walk(start,followlinks=False):
            for d in list(dirs):
                p=Path(base)/d
                if p.is_symlink():raise ValueError('refusing symlink: '+p.relative_to(root).as_posix())
                if d=='__pycache__':result.append(checked_tree(root,p,'python_bytecode'));dirs.remove(d)
    return sorted(result,key=lambda x:x['path'])

def apply(root,items):
    # Revalidate the complete plan before deleting any directory.
    now=plan(root)
    if now!=items:raise ValueError('cleanup plan changed; run dry-run again')
    for item in items:shutil.rmtree(root/item['path'])

def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--apply',action='store_true');ap.add_argument('--dry-run',action='store_true',help='explicit default; list without deleting')
    a=ap.parse_args(argv)
    if a.apply and a.dry_run:ap.error('choose --apply or --dry-run')
    items=plan(ROOT)
    if a.apply:apply(ROOT,items)
    print(json.dumps(dict(mode='apply' if a.apply else 'dry-run',entries=items,dependency_cache_touched=False,retained_data_touched=False),indent=2))
    return 0

if __name__=='__main__':
    try:raise SystemExit(main())
    except (ValueError,OSError) as exc:print('cleanup refused: '+str(exc));raise SystemExit(1)
