#!/usr/bin/env python3
"""Exact-source runner: snapshot source bytes, run strict (lean --trust=0) or
normal (lake build target) under /usr/bin/time -v, wall/RSS caps, raw log."""
import hashlib, json, os, shutil, subprocess, sys, time, datetime
mode, module, attempt = sys.argv[1], sys.argv[2], sys.argv[3]
root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
os.chdir(root)
vdir = 'verification/devin-f18-two-heavy-20261008'
src = module.replace('.', '/') + '.lean'
short = module.split('.')[-1]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
before = sha(src)
snap = f'{vdir}/{short}-{mode}-attempt{attempt}-source.lean'
shutil.copyfile(src, snap)
olean = f'.lake/devin-f18-two-heavy-{short}-{mode}-attempt{attempt}.olean'
if mode == 'strict':
    cmd = ['lake', 'env', 'lean', '--trust=0', '-M8000', '-o', olean, src]
else:
    cmd = ['lake', 'build', module]
log = f'{vdir}/{short}-{mode}-attempt{attempt}.stdout.txt'
tlog = f'{vdir}/{short}-{mode}-attempt{attempt}.time.txt'
WALL = 1800
t0 = time.time()
with open(log, 'wb') as out:
    p = subprocess.Popen(['/usr/bin/time', '-v', '-o', tlog] + cmd, stdout=out, stderr=subprocess.STDOUT)
    try:
        rc = p.wait(timeout=WALL); killed = False
    except subprocess.TimeoutExpired:
        p.kill(); rc = p.wait(); killed = True
el = time.time() - t0
txt = open(log, encoding='utf-8', errors='replace').read()
maxrss = None
for l in open(tlog):
    if 'Maximum resident set size' in l: maxrss = int(l.split(':')[1]) * 1024
own_warn = sum(1 for l in txt.splitlines() if l.startswith(src) and 'warning' in l) + \
    sum(1 for l in txt.splitlines() if ('warning: ' + src) in l)
rec = dict(mode=mode, module=module, attempt=int(attempt), command=cmd,
           time_wrapper=['/usr/bin/time', '-v'], cwd=root,
           recorded_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
           exit_code=rc, elapsed_seconds=el, time_maxrss_bytes=maxrss,
           rss_cap_bytes=8000 * 1024 * 1024 if mode == 'strict' else None,
           wall_cap_seconds=WALL, wall_cap_killed=killed,
           source=src, source_sha256_before=before, source_sha256_after=sha(src),
           source_snapshot=snap, log=log, log_sha256=sha(log),
           error_lines=sum(1 for l in txt.splitlines() if 'error' in l.lower() and src in l),
           own_warning_lines=own_warn,
           sorry_mentions=txt.count('sorry'),
           axiom_lines=[l for l in txt.splitlines() if 'depends on axioms' in l and short in l])
with open(f'{vdir}/runs.jsonl', 'a') as f: f.write(json.dumps(rec) + '\n')
print(json.dumps({k: rec[k] for k in ['mode','attempt','exit_code','elapsed_seconds','time_maxrss_bytes','source_sha256_before','error_lines','own_warning_lines']}))
