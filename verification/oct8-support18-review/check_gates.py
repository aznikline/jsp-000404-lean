from pathlib import Path
import subprocess,json,hashlib,re
out=Path('verification/oct8-support18-review')
audit=Path('verification/oct5-review/ProofAudit.lean')
count=len(re.findall(r'^#print axioms (\S+)',audit.read_text(),re.M))-1
assert count==2695
records=[]
for mode,expected in [('verified',0),('root',1)]:
 cmd=['python3','tools/check_proof_axioms_20261005.py','--audit',str(audit),'--log',str(out/'audit.stdout.txt'),'--mode',mode]
 p=subprocess.run(cmd,capture_output=True); d=json.loads(p.stdout)
 assert p.returncode==expected,(mode,p.returncode,p.stderr)
 assert d['declaration_count']==(count if mode=='verified' else 2)
 if mode=='root':assert d['failures']==[{'declaration':'Jsp404.sendov_lower','unexpected_axioms':['sorryAx']}]
 q=out/(mode+'-gate.json');q.write_bytes(p.stdout)
 records.append(dict(mode=mode,command=cmd,exit_code=p.returncode,declaration_count=d['declaration_count'],failures=d['failures'],stdout=str(q),stdout_sha256=hashlib.sha256(p.stdout).hexdigest()))
 print(json.dumps(records[-1]))
(out/'gates.json').write_text(json.dumps(records,indent=2)+'\n')
