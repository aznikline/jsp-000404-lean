"""Terminal API probe for T1 lane — same guarded run() shape as driver."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
V = Path(__file__).resolve().parent
W = V / 'worktree'; BASE = V.parent
GUARD = BASE / 'run_jsp_heavy.py'
LEAN = Path('/Users/wizout/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean')
OUT = W / '.lake/build/lib/lean'
def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for c in iter(lambda: f.read(1024*1024), b''): h.update(c)
    return h.hexdigest()
env = dict(os.environ)
pkgs = sorted((W / '.lake/packages').glob('*/.lake/build/lib/lean'))
env['LEAN_PATH'] = ':'.join(str(p.resolve()) for p in pkgs) + ':' + str(OUT) + ':' + str(LEAN.parent.parent / 'lib/lean')
def run(tag, argv):
    log = V / 'logs' / (tag + '.log'); log.parent.mkdir(exist_ok=True)
    if log.exists():
        st = str(time.time_ns())
        for p in (log, Path(str(log)+'.json')):
            if p.exists(): p.rename(Path(str(p)+'.prev.'+st))
    cmd = [sys.executable, str(GUARD), '--cwd', str(W), '--log', str(log), '--', str(LEAN), '-j1', '-M4096', *argv]
    waits = []
    while True:
        rc = subprocess.run(cmd, env=env, stdout=subprocess.DEVNULL).returncode
        r = json.loads(Path(str(log)+'.json').read_text())
        if r['status'] not in {'BUSY_LOCK','BUSY_EXISTING','LOW_MEMORY_PREFLIGHT'}: break
        waits.append(r)
        st = str(time.time_ns())
        Path(str(log)+'.json').rename(Path(str(log)+'.json.prev.'+st))
        if log.exists(): log.rename(Path(str(log)+'.prev.'+st))
        time.sleep(5)
    text = log.read_text() if log.exists() else ''
    within = r['max_rss_kib'] <= r['rss_cap_gib'] * 1024**2
    ok = rc == 0 and r['status'] == 'OK' and r['child_exit'] == 0 and r['elapsed_s'] <= 180 and within and not re.search(r'\berror:', text)
    return {'accepted': ok, 'receipt': r, 'wrapper_rc': rc, 'log': str(log),
            'log_sha256': sha(log) if log.exists() else None, 'guard_sha256': sha(GUARD),
            'resource_waits': waits}
state = json.loads((V/'batch_state.json').read_text())
probe = V / 'probe' / 'TerminalAPI.lean'
out = {'probe_sha256': sha(probe),
       'terminal_dep_fp': state['modules']['Jsp000404.R1DispatchT1']['dep_fp'],
       'context_sha256': state['context_sha256'],
       'normal': run('TerminalAPI_normal', [str(probe)]),
       'strict': run('TerminalAPI_strict', ['--trust=0', str(probe)])}
(V / 'terminal_probe_state.json').write_text(json.dumps(out, indent=1) + '\n')
print(json.dumps({k: out[k] for k in ('probe_sha256','terminal_dep_fp','context_sha256')}))
print('normal:', out['normal']['accepted'], out['normal']['receipt']['status'], out['normal']['receipt']['elapsed_s'])
print('strict:', out['strict']['accepted'], out['strict']['receipt']['status'], out['strict']['receipt']['elapsed_s'])
