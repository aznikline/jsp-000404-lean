from pathlib import Path
import json,subprocess,sys
base=Path(__file__).resolve().parent
p=json.loads((base/'compile-plan.json').read_text())
for m in p['order']:
 for stage in ('strict','normal'):
  print(json.dumps({'event':'START','module':m,'stage':stage}),flush=True)
  r=subprocess.run([sys.executable,str(base/'check.py'),m,stage])
  print(json.dumps({'event':'EXIT','module':m,'stage':stage,'exit_code':r.returncode}),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
print(json.dumps({'event':'ALL_STAGE_COMMANDS_PASSED','module_count':len(p['order']),'claim':'Read every actual checkpoint before acceptance'}),flush=True)
