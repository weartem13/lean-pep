"""Outer observer only: executes the unchanged consumer CLI, records returned locals."""
from pathlib import Path
import sys,json,time,runpy
root=Path(sys.argv[1]).resolve(); record=Path(sys.argv[2]).resolve();args=sys.argv[3:]
strategy=str(root/'tools/replay_structured_pg_two.py')
start=time.monotonic()
def profile(frame,event,arg):
 if frame.f_code.co_filename!=strategy:return
 name=frame.f_code.co_name
 if name=='build_candidate' and event in ('call','return'):
  item=dict(stage='candidate_started' if event=='call' else 'candidate_returned',
            wall_seconds=time.monotonic()-start,trial_count=len(frame.f_locals.get('trials',[])),
            trials=frame.f_locals.get('trials',[]),returned_candidate=event=='return' and arg is not None)
  record.write_text(json.dumps(item,indent=2)+'\n')
 return
sys.path.insert(0,str(root/'tools'));sys.argv=[str(root/'tools/replay_pg_certificate.py'),*args]
sys.setprofile(profile)
try:runpy.run_path(sys.argv[0],run_name='__main__')
finally:sys.setprofile(None)

