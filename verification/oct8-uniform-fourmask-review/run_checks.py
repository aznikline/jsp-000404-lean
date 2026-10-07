import sys,json,time,subprocess,os,signal,hashlib
from pathlib import Path
mode=sys.argv[1]
prep=json.loads(Path('.lake/oct8-uniform-fourmask-prep.json').read_text())
for path,key in [('Jsp000404.lean','root_after_sha256'),('verification/oct5-review/ProofAudit.lean','audit_after_sha256')]:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==prep[key],path
assert mode in ['full','audit']
for path,h in prep['new_source_sha256'].items():
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h,path
initial=subprocess.check_output(['ps','-axo','comm='],text=True)
assert not any(Path(line.strip()).name=='lean' for line in initial.splitlines()),'another Lean active'
out=Path('verification/oct8-uniform-fourmask-review');out.mkdir(parents=True,exist_ok=True)
cmd=['lake','build'] if mode=='full' else ['lake','env','lean','--trust=0','-M8000','-j1','verification/oct5-review/ProofAudit.lean']
log=out/(mode+'.stdout.txt')
assert not log.exists() and not (out/(mode+'.json')).exists(),'preserve previous attempt; use a fresh output directory'
t=time.monotonic();peak=0;cap=False;timeout=False;parallel=False;max_global=0
with log.open('wb') as f:
 p=subprocess.Popen(['/usr/bin/time','-l',*cmd],stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  rows={}
  for line in subprocess.run(['ps','-axo','pid=,ppid=,rss=,comm='],capture_output=True,text=True).stdout.splitlines():
   a=line.split(None,3)
   if len(a)==4:
    try:rows[int(a[0])]=(int(a[1]),int(a[2]),a[3])
    except ValueError:pass
  global_count=sum(Path(v[2]).name=='lean' for v in rows.values());max_global=max(max_global,global_count)
  if global_count>1:parallel=True
  ds={p.pid}; old=0
  while len(ds)!=old:
   old=len(ds);ds.update(k for k,v in rows.items() if v[0] in ds)
  for k in ds:
   if k in rows and Path(rows[k][2]).name=='lean':
    peak=max(peak,rows[k][1]*1024)
    if peak>8*1024**3:cap=True
  timeout=time.monotonic()-t>180
  if cap or timeout or parallel:os.killpg(p.pid,signal.SIGTERM)
  time.sleep(.15)
 rc=p.wait()
r=dict(max_global_lean_count=max_global,parallel_lean_cap_killed=parallel,mode=mode,command=cmd,exit_code=rc,elapsed_seconds=time.monotonic()-t,peak_lean_rss_bytes=peak,rss_cap_bytes=8*1024**3,rss_cap_killed=cap,timeout_seconds=180,timeout_killed=timeout,stdout=str(log),stdout_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
(out/(mode+'.json')).write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));s=log.read_text(errors='replace')
print(s[-1500:] if rc else '\n'.join(x for x in s.splitlines() if 'Built Jsp000404' in x or 'Build completed' in x)[-1000:])
sys.exit(rc)
