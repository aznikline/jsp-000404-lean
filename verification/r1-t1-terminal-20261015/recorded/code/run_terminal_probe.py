"""Run the independent original-API probe only after the root's full audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

V = Path(__file__).resolve().parent
W = V / 'worktree'
GUARD = V.parent / 'run_jsp_heavy.py'
ROOT = 'Jsp000404.R1DispatchT1'
P = V / 'probe/TerminalAPI.lean'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    s = json.loads((V / 'batch_state.json').read_text())
    root = s['modules'].get(ROOT, {})
    if s.get('current') or s.get('stopped') or root.get('state') != 'PASSED':
        raise SystemExit('Terminal probe refused: the complete root audit has not finished.')
    src = W / 'Jsp000404/R1DispatchT1.lean'
    if sha(src) != root['src_sha256']:
        raise SystemExit('Terminal probe refused: root source changed after audit.')
    pins = json.loads((V / 'root_source_pins.json').read_text())['modules']
    for module, expected in pins.items():
        path = W / (('ThirdParty/Sendov/' if module.startswith('JSP404.') else '') + module.replace('.', '/') + '.lean')
        if sha(path) != expected:
            raise SystemExit('Terminal probe refused: pinned source changed: ' + module)
        if s['modules'].get(module, {}).get('state') not in {'PASSED', 'AUDITED_NON_STD3', 'BORROWED', 'BORROWED_NON_STD3'}:
            raise SystemExit('Terminal probe refused: dependency audit pending: ' + module)
    lean = Path(s['context']['lean_path'].split(':')[-1]).parent.parent / 'bin/lean'
    env = dict(os.environ, LEAN_PATH=s['context']['lean_path'])
    result = {'probe_sha256': sha(P), 'terminal_dep_fp': root['dep_fp'],
              'context_sha256': s['context_sha256'], 'root_source_sha256': root['src_sha256'],
              'terminal_accepted': False}
    for phase in ('normal', 'strict'):
        log = V / 'logs' / ('RootTerminalAPI_' + phase + '.log')
        for path in (log, Path(str(log) + '.json')):
            if path.exists():
                path.rename(Path(str(path) + '.prev.' + str(time.time_ns())))
        argv = [str(lean), '-j1', '-M4096'] + (['--trust=0'] if phase == 'strict' else []) + [str(P)]
        cmd = [sys.executable, str(GUARD), '--cwd', str(W), '--log', str(log), '--', *argv]
        waits = []
        while True:
            rc = subprocess.run(cmd, env=env).returncode
            receipt = json.loads(Path(str(log) + '.json').read_text())
            if receipt['status'] not in {'BUSY_LOCK', 'BUSY_EXISTING', 'LOW_MEMORY_PREFLIGHT'}:
                break
            waits.append(receipt)
            stamp = str(time.time_ns())
            for path in (log, Path(str(log) + '.json')):
                if path.exists():
                    path.rename(Path(str(path) + '.prev.' + stamp))
            time.sleep(5)
        text = log.read_text() if log.exists() else ''
        accepted = (rc == 0 and receipt['status'] == 'OK' and receipt['child_exit'] == 0
                    and receipt['rss_cap_gib'] == 4 and receipt['max_rss_kib'] <= 4 * 1024**2
                    and receipt['elapsed_s'] <= 180 and not re.search(r'\berror[:(]', text))
        result[phase] = {'accepted': accepted, 'receipt': receipt, 'wrapper_rc': rc,
                         'log': str(log), 'log_sha256': sha(log) if log.exists() else None,
                         'guard_sha256': sha(GUARD), 'resource_waits': waits}
        (V / 'root_terminal_probe_state.json').write_text(json.dumps(result, indent=2) + '\n')
        if not accepted:
            raise SystemExit('Terminal probe failed in ' + phase + ': ' + receipt['status'])
    print('Both original-API probe runs finished; independent full acceptance is still required.')

if __name__ == '__main__':
    main()
