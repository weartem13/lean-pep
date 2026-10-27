#!/usr/bin/env python3
"""Read-only binding of the accepted PG1 pair; namespace-copy proofs, no recovery.
This deliberately has no solver, candidate generator, or alternative endpoint.
"""
import hashlib,json,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
INPUTS={
'data/cases/pg/one-step-exact/selected_exact.json':'8d1a4dc93f1d6306db88a57ff24ffb608ccd375d335da317a9964cf31c01c1f6',
'data/cases/pg/one-step-exact/selected_primal.json':'c266a455fae4d6b8916ea44093c87ad39f61aed31664d866be6b773f0a2d0dfa',
'data/cases/pg/one-step-exact/capture.json':'69ab11490086c9d6e704b6b6693d45e783a84ed61fe1c14519e423c4a608250b',
'data/cases/pg/one-step-exact/primal_observation.json':'bcb554e3eb8dca873f126f6fced3c84f31856ec12e9f0c22ae46b2b14edac79e',
'data/cases/pg/one-step-exact/UpperReplay.lean':'9d871ff84b6f46b12e49c0ec44f49fb4afdce3d010c62b45c96effd46f2b4aeb',
'data/cases/pg/one-step-exact/PrimalReplay.lean':'899081b9a9641cab239f8546eb7bbac224fa10a4f12d0576b4af4c9a72edacb8',
}
COPIES=[('data/cases/pg/one-step-exact/UpperReplay.lean','LeanPEP.Imported.Structured.PGOne001','LeanPEP.Imported.C14PGOneUpper'),('data/cases/pg/one-step-exact/PrimalReplay.lean','LeanPEP.Imported.PGOnePrimal001','LeanPEP.Imported.C14PGOnePrimal')]
def digest(b):return hashlib.sha256(b).hexdigest()
def validate(root):
    for path,sha in INPUTS.items():
        if digest((root/path).read_bytes())!=sha:raise ValueError('accepted input changed: '+path)
    return dict(INPUTS)
def renamed(text,old,new):
    return text.replace(old,new).replace('\n\n','\nset_option autoImplicit false\n\n',1)
def materialize(root,directory):
    hashes=validate(root)
    outputs={directory/(new.rsplit('.',1)[-1]+'.lean'):renamed((root/path).read_text(),old,new) for path,old,new in COPIES}
    if any(p.exists() for p in outputs):raise ValueError('refuse to overwrite retained proof module')
    directory.mkdir(parents=True,exist_ok=True)
    for p,t in outputs.items():p.write_text(t)
    return dict(input_hashes=hashes,solver_calls=0,numerical_recovery=False,live_capture_performed=False,copies=[dict(old_file=path,old_namespace=old,new_namespace=new,new_file=str(directory/(new.rsplit('.',1)[-1]+'.lean')),transformation='namespace alpha-renaming plus autoImplicit false only',new_sha256=digest(outputs[directory/(new.rsplit('.',1)[-1]+'.lean')].encode())) for path,old,new in COPIES])
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--binding',type=Path,required=True);a=p.parse_args()
    result=materialize(ROOT,a.output);a.binding.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
