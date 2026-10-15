"""Local full T2 kernel lane. Every compiler call uses the original 4GiB guard."""
import collections
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
BASE = V.parent
GUARD = BASE / 'run_jsp_heavy.py'
LEAN = Path('/Users/wizout/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean')
OUT = W / '.lake/build/lib/lean'
STATE = V / 'batch_state.json'
STD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()

def source(m):
    return W / (('ThirdParty/Sendov/' if m.startswith('JSP404.') else '') + m.replace('.', '/') + '.lean')

def imports(m):
    return re.findall(r'^import\s+(\S+)', source(m).read_text(), re.M)

def artifact(m, suffix):
    return OUT / (m.replace('.', '/') + suffix)

def write_state():
    c = collections.Counter(r.get('state') for r in state['modules'].values())
    state['counts'] = dict(c)
    state['updated'] = time.time()
    tmp = STATE.with_suffix('.tmp')
    tmp.write_text(json.dumps(state, indent=1) + '\n')
    tmp.replace(STATE)

def run(tag, argv):
    log = V / 'logs' / (tag + '.log')
    log.parent.mkdir(exist_ok=True)
    if log.exists():
        stamp = str(time.time_ns())
        for p in (log, Path(str(log) + '.json')):
            if p.exists(): p.rename(Path(str(p) + '.prev.' + stamp))
    free_text = subprocess.check_output(['memory_pressure'], text=True)
    free_match = re.search(r'System-wide memory free percentage:\s*(\d+)%', free_text)
    calibrated = ['--mapped-rss-gib', '6'] if free_match and int(free_match[1]) >= 55 else []
    cmd = [sys.executable, str(GUARD), '--cwd', str(W), '--log', str(log), *calibrated, '--', str(LEAN), '-j1', '-M4096', *argv]
    waits = []
    while True:
        rc = subprocess.run(cmd, env=env, stdout=subprocess.DEVNULL).returncode
        receipt = json.loads(Path(str(log) + '.json').read_text())
        if receipt['status'] not in {'BUSY_LOCK', 'BUSY_EXISTING', 'LOW_MEMORY_PREFLIGHT'}: break
        waits.append(receipt)
        state['waiting_resource'] = {'tag': tag, 'status': receipt['status'], 'at': time.time()}
        write_state()
        stamp = str(time.time_ns())
        Path(str(log) + '.json').rename(Path(str(log) + '.json.prev.' + stamp))
        if log.exists(): log.rename(Path(str(log) + '.prev.' + stamp))
        time.sleep(5)
        if (V / 'STOP_AFTER_CURRENT').exists(): break
    state.pop('waiting_resource', None)
    text = log.read_text() if log.exists() else ''
    within_memory = receipt['max_rss_kib'] <= receipt['rss_cap_gib'] * 1024**2
    if receipt.get('mapped_rss_requested_gib'):
        within_memory = within_memory and receipt.get('max_footprint_bytes') is not None and receipt['max_footprint_bytes'] <= 4 * 1024**3
    ok = rc == 0 and receipt['status'] == 'OK' and receipt['child_exit'] == 0 and receipt['elapsed_s'] <= 180 and within_memory and not re.search(r'\berror:', text)
    return {'accepted': ok, 'receipt': receipt, 'wrapper_rc': rc, 'log': str(log), 'log_sha256': sha(log) if log.exists() else None, 'guard_sha256': sha(GUARD), 'resource_waits': waits}

def valid(record):
    if not isinstance(record, dict): return False
    try:
        r = json.loads(Path(record['log'] + '.json').read_text())
        args = r['argv']
        memory_ok = r['rss_cap_gib'] == 4 and r['max_rss_kib'] <= 4 * 1024**2
        if r.get('mapped_rss_requested_gib') == 6:
            memory_ok = r['rss_cap_gib'] <= 6 and r['max_rss_kib'] <= r['rss_cap_gib'] * 1024**2 and r['footprint_cap_gib'] == 4 and r['max_footprint_bytes'] is not None and r['max_footprint_bytes'] <= 4 * 1024**3 and r['preflight_free_percent'] >= 55
        return record['accepted'] and r == record['receipt'] and sha(record['log']) == record['log_sha256'] and record['guard_sha256'] == sha(GUARD) and r['status'] == 'OK' and r['child_exit'] == 0 and r['exit_code'] == 0 and r['elapsed_s'] <= 180 and memory_ok and r['wall_cap_s'] == 180 and r['nice'] == 15 and args[:3] == [str(LEAN), '-j1', '-M4096'] and r['cwd'] == str(W)
    except (OSError, KeyError, ValueError, TypeError): return False

def audit(group, split_on_limit=True):
    name = 'Audit' + str(len(state['audits'])).zfill(4)
    p = V / 'probe' / (name + '.lean')
    p.parent.mkdir(exist_ok=True)
    body = 'import Lean\n' + ''.join('import ' + m + '\n' for m in group) + '''open Lean Elab Command
elab "#localaudit " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module missing"
  let names := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n _ =>
    if env.getModuleIdxFor? n == some idx && !n.isInternalDetail then acc.push n else acc
  logInfo m!"AUDITMOD {m.getId} {names.size}"
  for n in names do
    let ax ← collectAxioms n
    logInfo m!"AUDITDECL {m.getId} {n} AXIOMS {ax.toList}"
''' + ''.join('#localaudit ' + m + '\n' for m in group)
    p.write_text(body)
    a = run(name, ['--trust=0', str(p)])
    if a['receipt']['status'] in {'RSS_LIMIT', 'FOOTPRINT_LIMIT', 'WALL_LIMIT'} and len(group) > 1 and split_on_limit:
        a.update(probe=str(p), probe_sha256=sha(p), modules=group, split_required=True)
        state['audits'][name] = a
        write_state()
        middle = len(group) // 2
        audit(group[:middle]); audit(group[middle:])
        return
    text = Path(a['log']).read_text()
    rows = re.findall(r'AUDITDECL (\S+) (\S+) AXIOMS \[([^\]]*)\]', text)
    per = collections.Counter(m for m, _, _ in rows)
    headers = {m: int(n) for m, n in re.findall(r'AUDITMOD (\S+) (\d+)', text)}
    bad = {m for m, _, ax in rows if not {x.strip() for x in ax.split(',') if x.strip()} <= STD}
    a.update(probe=str(p), probe_sha256=sha(p), modules=group, srcs={m: sha(source(m)) for m in group}, dep_fps={m: state['modules'][m]['dep_fp'] for m in group}, declarations=dict(per), non_std3=sorted(bad))
    state['audits'][name] = a
    for m in group:
        state['modules'][m]['audit'] = name
        import_only = m in {'Jsp000404.K3bGeometry', 'Jsp000404.K3bGeometryPart3', 'Jsp000404.S7Defs'}
        complete = headers.get(m) == per[m] and (per[m] > 0 or import_only)
        state['modules'][m]['state'] = ('PASSED' if m not in bad else 'AUDITED_NON_STD3') if a['accepted'] and complete else 'AUDIT_FAILED'
    write_state()

def closure(root):
    order, seen, active = [], set(), set()
    def visit(m):
        if not source(m).exists(): return
        if m in active: raise RuntimeError('import cycle: ' + m)
        if m in seen: return
        active.add(m)
        for d in imports(m): visit(d)
        active.remove(m); seen.add(m); order.append(m)
    visit(root)
    return order

env = dict(os.environ)
package_dirs = sorted((W / '.lake/packages').glob('*/.lake/build/lib/lean'))
env['LEAN_PATH'] = ':'.join(str(p.resolve()) for p in package_dirs) + ':' + str(OUT) + ':' + str(LEAN.parent.parent / 'lib/lean')
packages = []
for p in json.loads((W / 'lake-manifest.json').read_text())['packages']:
    folder = W / '.lake/packages' / p['name']
    rev = subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(folder), 'status', '--porcelain'], text=True)
    if rev != p['rev'] or dirty: raise RuntimeError('package revision/cleanliness mismatch: ' + p['name'])
    h = hashlib.sha256(); root = folder / '.lake/build/lib/lean'
    for f in sorted(root.rglob('*.olean')):
        h.update(str(f.relative_to(root)).encode()); h.update(sha(f).encode())
    packages.append({'name': p['name'], 'rev': rev, 'olean_tree_sha256': h.hexdigest()})
context = {'toolchain': (W / 'lean-toolchain').read_text().strip(), 'lakefile': sha(W / 'lakefile.lean'), 'manifest': sha(W / 'lake-manifest.json'), 'lean': sha(LEAN), 'guard': sha(GUARD), 'lean_path': env['LEAN_PATH'], 'packages': packages, 'source_manifest': sha(BASE / 't2-quota-recovery-20261013/OVERLAY_MANIFEST.json')}
ctx = hashlib.sha256(json.dumps(context, sort_keys=True).encode()).hexdigest()
state = json.loads(STATE.read_text()) if STATE.exists() else {'modules': {}, 'audits': {}}
order = closure('Jsp000404.R1DispatchT2')
state.update(pid=os.getpid(), root='Jsp000404.R1DispatchT2', closure_size=len(order), context=context, context_sha256=ctx, started=time.time())
state.pop('stopped', None)
pending, failures, fp = [], set(), {}
write_state()
for m in order:
    src_sha = sha(source(m))
    dependencies = [(d, fp.get(d), sha(artifact(d, '.olean')) if artifact(d, '.olean').exists() else None) for d in imports(m)]
    dep_fp = hashlib.sha256(json.dumps([src_sha, ctx, dependencies]).encode()).hexdigest()
    fp[m] = dep_fp
    old = state['modules'].get(m, {})
    if any(d in failures for d in imports(m)):
        failures.add(m); state['modules'][m] = {'state': 'SKIPPED_DEP_FAILED', 'src_sha256': src_sha}; continue
    reusable = old.get('src_sha256') == src_sha and old.get('dep_fp') == dep_fp and old.get('ctx') == ctx and valid(old.get('normal', {})) and valid(old.get('strict', {})) and artifact(m, '.olean').exists() and old.get('olean_sha256') == sha(artifact(m, '.olean'))
    if reusable:
        a = state['audits'].get(old.get('audit'), {})
        if not (valid(a) and a.get('srcs', {}).get(m) == src_sha and a.get('dep_fps', {}).get(m) == dep_fp and a.get('probe') and sha(a['probe']) == a.get('probe_sha256')):
            old['state'] = 'PASSED_UNAUDITED'; pending.append(m)
    else:
        state['current'] = m; write_state(); print('RUN', m, state['counts'], flush=True)
        artifact(m, '.olean').parent.mkdir(parents=True, exist_ok=True)
        normal_only_reuse = old.get('src_sha256') == src_sha and old.get('dep_fp') == dep_fp and old.get('ctx') == ctx and valid(old.get('normal', {})) and artifact(m, '.olean').exists() and old.get('olean_sha256') == sha(artifact(m, '.olean'))
        n = old['normal'] if normal_only_reuse else run(m + '_normal', ['-o', str(artifact(m, '.olean')), '-i', str(artifact(m, '.ilean')), str(source(m))])
        s = run(m + '_strict', ['--trust=0', str(source(m))]) if n['accepted'] else None
        rec = {'src_sha256': src_sha, 'dep_fp': dep_fp, 'ctx': ctx, 'normal': n, 'strict': s, 'state': 'PASSED_UNAUDITED' if n['accepted'] and s and s['accepted'] else 'FAILED'}
        if old: rec['history'] = old.get('history', []) + [{k: v for k, v in old.items() if k != 'history'}]
        state['modules'][m] = rec
        if n['accepted']: rec['olean_sha256'] = sha(artifact(m, '.olean'))
        if rec['state'] == 'FAILED':
            failures.add(m); write_state()
            state['stopped'] = {'reason': n['receipt']['status'] if not n['accepted'] else s['receipt']['status'], 'module': m}
            break
        rec['olean_sha256'] = sha(artifact(m, '.olean')); pending.append(m)
    if len(pending) >= 8:
        audit(pending); pending = []
    if (V / 'STOP_AFTER_CURRENT').exists():
        state['stopped'] = {'reason': 'STOP_AFTER_CURRENT', 'module': m}; break
    write_state()
if pending: audit(pending)
state['current'] = None
state['finished'] = time.time()
write_state()
print('END', state['counts'], state.get('stopped'), flush=True)
