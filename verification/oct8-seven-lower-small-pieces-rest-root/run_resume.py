from pathlib import Path
import hashlib,json,subprocess,sys
base=Path(__file__).resolve().parent
plan=json.loads((base/'compile-plan.json').read_text())
for m in plan['order']:
 source=base.parents[1]/plan['modules'][m]['source']
 h=hashlib.sha256(source.read_bytes()).hexdigest()
 assert h==plan['modules'][m]['approved_source_sha256']
 cp=base/m.split('.')[-1]/'checkpoint.json'
 for stage in ('strict','normal'):
  d=json.loads(cp.read_text()) if cp.exists() else {'attempts':[]}
  accepted=[a for a in d['attempts'] if a['stage']==stage and a['status']=='PASS' and a['exit_code']==0 and a['resource_stop'] is None and a['source_sha256']==h and a['selected_standard_axioms_gate'] and (stage!='normal' or a['own_target_built'])]
  if accepted:
   print(json.dumps({'event':'REUSE_CURRENT_ACCEPTED','module':m,'stage':stage,'attempt':accepted[-1]['attempt']}),flush=True);continue
  print(json.dumps({'event':'START','module':m,'stage':stage}),flush=True)
  r=subprocess.run([sys.executable,str(base/'check.py'),m,stage])
  print(json.dumps({'event':'EXIT','module':m,'stage':stage,'exit_code':r.returncode}),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
print(json.dumps({'event':'ALL_CURRENT_STAGES_ACCEPTED','modules':len(plan['order'])}),flush=True)
