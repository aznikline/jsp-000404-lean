import sys,json,time,subprocess,os,signal,hashlib
from pathlib import Path
mode=sys.argv[1]
out=Path('verification/oct8-outer-critical21-review');out.mkdir(parents=True,exist_ok=True)
cmd=['lake','build'] if mode=='full' else ['lake','env','lean','--trust=0','-M8000','verification/oct5-review/ProofAudit.lean']
log=out/(mode+'.stdout.txt'); t=time.monotonic();peak=0;cap=False;timeout=False
with log.open('wb') as f:
 p=subprocess.Popen(['/usr/bin/time','-l',*cmd],stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  rows={}
  for line in subprocess.run(['ps','-axo','pid=,ppid=,rss=,comm='],capture_output=True,text=True).stdout.splitlines():
   a=line.split(None,3)
   if len(a)==4:
    try:rows[int(a[0])]=(int(a[1]),int(a[2]),a[3])
    except ValueError:pass
  ds={p.pid}; old=0
  while len(ds)!=old:
   old=len(ds);ds.update(k for k,v in rows.items() if v[0] in ds)
  for k in ds:
   if k in rows and Path(rows[k][2]).name=='lean':
    peak=max(peak,rows[k][1]*1024)
    if peak>8*1024**3:cap=True
  timeout=time.monotonic()-t>300
  if cap or timeout:os.killpg(p.pid,signal.SIGTERM)
  time.sleep(.15)
 rc=p.wait()
r=dict(mode=mode,command=cmd,exit_code=rc,elapsed_seconds=time.monotonic()-t,peak_lean_rss_bytes=peak,rss_cap_bytes=8*1024**3,rss_cap_killed=cap,timeout_seconds=300,timeout_killed=timeout,stdout=str(log),stdout_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
(out/(mode+'.json')).write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));s=log.read_text(errors='replace')
print(s[-1500:] if rc else '\n'.join(x for x in s.splitlines() if 'Built Jsp000404' in x or 'Build completed' in x)[-1000:])
sys.exit(rc)
