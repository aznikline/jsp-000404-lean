"""Fresh full-566 T1 reproduction lane. No borrowing; every module recompiled
under the original 4GiB guard, then the original-API probe runs normal+--trust=0.

Stages:
  --check-config   verify toolchain/guard/project pins only (NOT a pass)
  --batch          compile all 566 modules + audits only (NOT a pass)
  (default)        config + batch + terminal probe = full reproduction

Exit status: nonzero on any failure, stop, or incomplete stage.
"""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

V = Path(__file__).resolve().parent          # reproduce/: state+logs+build here
W = V.parents[2]                             # worktree root
OUT = V / 'build' / 'lib' / 'lean'           # independent OUT; never touches verified artifacts

def resolve_guard():
    """The guard's heavy.lock lives beside its file. Only the original
    .coordination/run_jsp_heavy.py (or JSP404_HEAVY_GUARD) shares the real
    lock with other lanes; the pack copy would create a second lock.
    Returns (path, origin); origin 'pack-copy' means unshared lock."""
    if os.environ.get('JSP404_HEAVY_GUARD'):
        return Path(os.environ['JSP404_HEAVY_GUARD']), 'env:JSP404_HEAVY_GUARD'
    for anc in Path(__file__).resolve().parents:
        cand = (anc / 'run_jsp_heavy.py') if anc.name == '.coordination' \
            else (anc / '.coordination' / 'run_jsp_heavy.py')
        if cand.is_file():
            return cand, 'ancestor:' + str(anc)
    pack_copy = V.parent / 'run_jsp_heavy.py'
    if pack_copy.is_file():
        return pack_copy, 'pack-copy-unshared-lock'
    return None, 'missing'

GUARD, GUARD_ORIGIN = resolve_guard()
STATE = V / 'repro_state.json'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
EMPTY = {'Jsp000404.K3bGeometry', 'Jsp000404.K3bGeometryPart3',
         'Jsp000404.S7Defs', 'Jsp000404.DeletionRigidity', 'Jsp000404.R3WitnessDag'}
BASELINE = {
    'Jsp000404.Section4Legality': {'Jsp404.staircase_of_legality'},
    'Jsp000404.Deletion': {'Jsp404.exists_removable_hull_vertex', 'Jsp404.exists_removable_vertex'},
    'Jsp000404.GeometricDeletion': {'Jsp404.maxGap_boundary_emission'},
}
ROOT_MOD = 'Jsp000404.R1DispatchT1'

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def source(m):
    return W / (('ThirdParty/Sendov/' if m.startswith('JSP404.') else '') + m.replace('.', '/') + '.lean')

def imports(m):
    return re.findall(r'^import\s+(\S+)', source(m).read_text(), re.M)

def artifact(m, suffix):
    return OUT / (m.replace('.', '/') + suffix)

def elan_lean():
    out = subprocess.check_output(['elan', 'which', 'lean'], text=True,
                                  cwd=str(W)).strip()
    return Path(out)

def closure(root):
    order, seen, active = [], set(), set()
    def visit(m):
        if not source(m).exists():
            need(not m.startswith(('Jsp000404.', 'JSP404.')), 'missing project source: ' + m)
            return
        need(m not in active, 'import cycle: ' + m)
        if m in seen:
            return
        active.add(m)
        for d in imports(m):
            visit(d)
        active.remove(m)
        seen.add(m)
        order.append(m)
    visit(root)
    return order

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
            if p.exists():
                p.rename(Path(str(p) + '.prev.' + stamp))
    cmd = [sys.executable, str(GUARD), '--cwd', str(W), '--log', str(log),
           '--', str(LEAN), '-j1', '-M4096', *argv]
    waits = []
    while True:
        rc = subprocess.run(cmd, env=env, stdout=subprocess.DEVNULL).returncode
        receipt = json.loads(Path(str(log) + '.json').read_text())
        if receipt['status'] not in {'BUSY_LOCK', 'BUSY_EXISTING', 'LOW_MEMORY_PREFLIGHT'}:
            break
        waits.append(receipt)
        stamp = str(time.time_ns())
        Path(str(log) + '.json').rename(Path(str(log) + '.json.prev.' + stamp))
        if log.exists():
            log.rename(Path(str(log) + '.prev.' + stamp))
        time.sleep(5)
        if (V / 'STOP_AFTER_CURRENT').exists():
            break
    text = log.read_text() if log.exists() else ''
    within = receipt['max_rss_kib'] <= receipt['rss_cap_gib'] * 1024**2
    ok = (rc == 0 and receipt['status'] == 'OK' and receipt['child_exit'] == 0
          and receipt['elapsed_s'] <= 180 and within and receipt['rss_cap_gib'] == 4
          and not receipt.get('mapped_rss_requested_gib')
          and not re.search(r'\berror:', text))
    return {'accepted': ok, 'receipt': receipt, 'wrapper_rc': rc, 'log': str(log),
            'log_sha256': sha(log) if log.exists() else None,
            'guard_sha256': sha(GUARD), 'resource_waits': waits, 'text': text}

def valid(record):
    if not isinstance(record, dict):
        return False
    try:
        r = json.loads(Path(record['log'] + '.json').read_text())
        return (record['accepted'] and r == record['receipt']
                and sha(record['log']) == record['log_sha256']
                and record['guard_sha256'] == sha(GUARD)
                and r['status'] == 'OK' and r['child_exit'] == 0 and r['exit_code'] == 0
                and r['elapsed_s'] <= 180 and r['wall_cap_s'] == 180 and r['nice'] == 15
                and r['rss_cap_gib'] == 4 and not r.get('mapped_rss_requested_gib')
                and r['max_rss_kib'] <= 4 * 1024**2
                and r['argv'][:3] == [str(LEAN), '-j1', '-M4096'] and r['cwd'] == str(W))
    except (OSError, KeyError, ValueError, TypeError):
        return False

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
        audit(group[:middle])
        audit(group[middle:])
        return
    text = Path(a['log']).read_text()
    rows = re.findall(r'AUDITDECL (\S+) (\S+) AXIOMS \[([^\]]*)\]', text)
    per = collections.Counter(m for m, _, _ in rows)
    headers = {m: int(n) for m, n in re.findall(r'AUDITMOD (\S+) (\d+)', text)}
    bad = {m for m, _, ax in rows if not {x.strip() for x in ax.split(',') if x.strip()} <= STD}
    a.update(probe=str(p), probe_sha256=sha(p), modules=group,
             srcs={m: sha(source(m)) for m in group},
             dep_fps={m: state['modules'][m]['dep_fp'] for m in group},
             declarations=dict(per), non_std3=sorted(bad))
    state['audits'][name] = a
    for m in group:
        state['modules'][m]['audit'] = name
        declarations = [(n, ax) for module, n, ax in rows if module == m]
        bad_names = {n for n, ax in declarations
                     if not {x.strip() for x in ax.split(',') if x.strip()} <= STD}
        complete = (headers.get(m) == per.get(m, 0)
                    and (per.get(m, 0) > 0 or m in EMPTY)
                    and bad_names == BASELINE.get(m, set()))
        state['modules'][m]['state'] = ('PASSED' if m not in bad else 'AUDITED_NON_STD3') \
            if a['accepted'] and complete else 'AUDIT_FAILED'
    write_state()

# ---------------- configuration ----------------
LEAN = elan_lean()
need(LEAN.exists(), 'elan did not resolve a lean binary')
recorded = json.loads((V.parent / 'recorded/root_state_snapshot.json').read_text())
recorded_ctx = recorded['context']
pins = json.loads((V.parent / 'recorded/root_input_acceptance.json').read_text())['modules']

env = dict(os.environ)
package_dirs = sorted((W / '.lake/packages').glob('*/.lake/build/lib/lean'))
env['LEAN_PATH'] = ':'.join(str(p.resolve()) for p in package_dirs) + ':' + str(OUT) \
    + ':' + str(LEAN.parent.parent / 'lib/lean')
packages = []
for p in json.loads((W / 'lake-manifest.json').read_text())['packages']:
    folder = W / '.lake/packages' / p['name']
    rev = subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(folder), 'status', '--porcelain'], text=True)
    need(rev == p['rev'] and not dirty, 'package revision/cleanliness mismatch: ' + p['name'])
    h = hashlib.sha256()
    root = folder / '.lake/build/lib/lean'
    for f in sorted(root.rglob('*.olean')):
        h.update(str(f.relative_to(root)).encode())
        h.update(sha(f).encode())
    packages.append({'name': p['name'], 'rev': rev, 'olean_tree_sha256': h.hexdigest()})
context = {'toolchain': (W / 'lean-toolchain').read_text().strip(),
           'lakefile': sha(W / 'lakefile.lean'), 'manifest': sha(W / 'lake-manifest.json'),
           'lean': sha(LEAN), 'guard': sha(GUARD) if GUARD else None, 'lean_path': env['LEAN_PATH'],
           'packages': packages}
ctx = hashlib.sha256(json.dumps(context, sort_keys=True).encode()).hexdigest()
order = closure(ROOT_MOD)

ap = argparse.ArgumentParser()
ap.add_argument('--check-config', action='store_true')
ap.add_argument('--batch', action='store_true')
args = ap.parse_args()

config_report = {
    'lean_resolved': str(LEAN),
    'toolchain': context['toolchain'] == recorded_ctx['toolchain'],
    'lakefile': context['lakefile'] == recorded_ctx['lakefile'],
    'manifest': context['manifest'] == recorded_ctx['manifest'],
    'lean_binary_sha': context['lean'] == recorded_ctx['lean'],
    'guard_sha': context['guard'] == recorded_ctx['guard'],
    'guard_origin': GUARD_ORIGIN,
    'guard_shares_original_lock': GUARD_ORIGIN.startswith(('env:', 'ancestor:')),
    'platform': sys.platform,
    'packages': context['packages'] == recorded_ctx['packages'],
    'closure_is_566': len(order) == 566,
    'all_sources_pinned': all(source(m).exists() and sha(source(m)) == pins[m] for m in order),
    'pins_cover_closure': set(order) == set(pins),
}
print(json.dumps(config_report, indent=1))
config_ok = (all(v is True for k, v in config_report.items()
                 if k not in ('lean_resolved', 'guard_origin', 'platform'))
             and config_report['platform'] == 'darwin')
if args.check_config:
    print('CHECK_CONFIG_ONLY: configuration verified' if config_ok
          else 'CHECK_CONFIG_FAILED', flush=True)
    sys.exit(0 if config_ok else 1)
if not config_ok:
    print('NOT_READY: see config_report (guard_origin=' + str(GUARD_ORIGIN)
          + '); no run performed', flush=True)
    sys.exit(1)
need(GUARD_ORIGIN.startswith(('env:', 'ancestor:')),
     'only the pack guard copy exists; its heavy.lock is NOT shared with other'
     ' lanes — set JSP404_HEAVY_GUARD or run inside the original checkout')

state = json.loads(STATE.read_text()) if STATE.exists() else {'modules': {}, 'audits': {}}
state.update(pid=os.getpid(), root=ROOT_MOD, closure_size=len(order),
             context=context, context_sha256=ctx, started=time.time(),
             mode='fresh_full_566_no_borrow')
state.pop('stopped', None)
write_state()

# ---------------- batch ----------------
pending, failures, fp = [], set(), {}
write_state()
stopped = None
for m in order:
    src_sha = sha(source(m))
    dependencies = [(d, fp.get(d), sha(artifact(d, '.olean')) if artifact(d, '.olean').exists() else None)
                    for d in imports(m)]
    dep_fp = hashlib.sha256(json.dumps([src_sha, ctx, dependencies]).encode()).hexdigest()
    fp[m] = dep_fp
    old = state['modules'].get(m, {})
    if any(d in failures for d in imports(m)):
        failures.add(m)
        state['modules'][m] = {'state': 'SKIPPED_DEP_FAILED', 'src_sha256': src_sha}
        continue
    reusable = (old.get('src_sha256') == src_sha and old.get('dep_fp') == dep_fp
                and old.get('ctx') == ctx and valid(old.get('normal', {}))
                and valid(old.get('strict', {})) and artifact(m, '.olean').exists()
                and old.get('olean_sha256') == sha(artifact(m, '.olean')))
    if reusable:
        a = state['audits'].get(old.get('audit'), {})
        if not (valid(a) and a.get('srcs', {}).get(m) == src_sha
                and a.get('dep_fps', {}).get(m) == dep_fp and a.get('probe')
                and sha(a['probe']) == a.get('probe_sha256')):
            old['state'] = 'PASSED_UNAUDITED'
            pending.append(m)
    else:
        state['current'] = m
        write_state()
        print('RUN', m, state['counts'], flush=True)
        artifact(m, '.olean').parent.mkdir(parents=True, exist_ok=True)
        n_ok = (old.get('src_sha256') == src_sha and old.get('dep_fp') == dep_fp
                and old.get('ctx') == ctx and valid(old.get('normal', {}))
                and artifact(m, '.olean').exists()
                and old.get('olean_sha256') == sha(artifact(m, '.olean')))
        n = old['normal'] if n_ok else run(m + '_normal',
            ['-o', str(artifact(m, '.olean')), '-i', str(artifact(m, '.ilean')), str(source(m))])
        s = run(m + '_strict', ['--trust=0', str(source(m))]) if n['accepted'] else None
        rec = {'src_sha256': src_sha, 'dep_fp': dep_fp, 'ctx': ctx,
               'normal': n, 'strict': s,
               'state': 'PASSED_UNAUDITED' if n['accepted'] and s and s['accepted'] else 'FAILED'}
        if old:
            rec['history'] = old.get('history', []) + [{k: v for k, v in old.items() if k != 'history'}]
        state['modules'][m] = rec
        if n['accepted']:
            rec['olean_sha256'] = sha(artifact(m, '.olean'))
        if rec['state'] == 'FAILED':
            failures.add(m)
            write_state()
            stopped = {'reason': n['receipt']['status'] if not n['accepted'] else s['receipt']['status'],
                       'module': m}
            state['stopped'] = stopped
            break
        rec['olean_sha256'] = sha(artifact(m, '.olean'))
        pending.append(m)
    if len(pending) >= 8:
        audit(pending)
        pending = []
    if (V / 'STOP_AFTER_CURRENT').exists():
        stopped = {'reason': 'STOP_AFTER_CURRENT', 'module': m}
        state['stopped'] = stopped
        break
    write_state()
if pending:
    audit(pending)
state['current'] = None
state['finished'] = time.time()
write_state()
counts = state['counts']
print('BATCH_END', counts, stopped, flush=True)
failed = {k: v for k, v in counts.items()
          if k not in ('PASSED', 'AUDITED_NON_STD3')}
if stopped or counts.get('PASSED', 0) + counts.get('AUDITED_NON_STD3', 0) != len(order):
    print('BATCH_INCOMPLETE: not a successful reproduction', file=sys.stderr)
    sys.exit(1)
need({m for m, r in state['modules'].items() if r['state'] == 'AUDITED_NON_STD3'} == set(BASELINE),
     'baseline admission inventory differs')
if args.batch:
    print('BATCH_ONLY_COMPLETE: all', len(order), 'modules compiled+audited;'
          ' terminal probe NOT run — not a full pass', flush=True)
    sys.exit(0)

# ---------------- terminal probe ----------------
probe = V / 'probe' / 'TerminalAPI.lean'
need(probe.exists() and sha(probe) ==
     json.loads((V.parent / 'recorded/root_probe_pin.json').read_text())['probe_sha256'],
     'original-API probe source differs from Root pin')
pn = run('TerminalAPI_normal', [str(probe)])
ps = run('TerminalAPI_strict', ['--trust=0', str(probe)])
state['terminal_probe'] = {'normal': {k: v for k, v in pn.items() if k != 'text'},
                           'strict': {k: v for k, v in ps.items() if k != 'text'},
                           'probe_sha256': sha(probe),
                           'terminal_dep_fp': fp.get(ROOT_MOD),
                           'context_sha256': ctx}
write_state()
need(pn['accepted'] and ps['accepted'], 'terminal probe execution failed')
bad = []
for text, phase in ((pn['text'], 'normal'), (ps['text'], 'strict')):
    for name in ('r1_seven_phi22_terminal', 'r1_phi22_all_defect3'):
        ax = re.findall(r"'Jsp404\." + name + r"' depends on axioms: \[([^\]]*)\]", text)
        if len(ax) != 1 or not {a.strip() for a in ax[0].split(',') if a.strip()} <= STD:
            bad.append((phase, name, ax))
need(not bad, 'terminal axiom closure is not Std3: ' + str(bad))
print('FULL_REPRODUCTION_COMPLETE: 566 fresh modules + original-API terminal probe; Std3.', flush=True)
sys.exit(0)
