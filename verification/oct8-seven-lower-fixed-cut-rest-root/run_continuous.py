from pathlib import Path
import json,subprocess,sys,time
base=Path(__file__).resolve().parent
p=json.loads((base/'compile-plan.json').read_text())
for module in p['order']:
 for stage in ('strict','normal'):
  print(json.dumps({'event':'START','module':module,'stage':stage}),flush=True)
  r=subprocess.run([sys.executable,str(base/'check.py'),module,stage])
  print(json.dumps({'event':'EXIT','module':module,'stage':stage,'exit_code':r.returncode}),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
print(json.dumps({'event':'ALL_STAGE_COMMANDS_PASSED','modules':len(p['order']),'claim':'Read actual checkpoints before proof acceptance'}),flush=True)
