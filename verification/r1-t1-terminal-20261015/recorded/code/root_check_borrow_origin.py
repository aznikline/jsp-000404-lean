"""Independent raw-artifact verifier; partial output never accepts the terminal."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess

V = Path('/Users/wizout/op/learn/sunyuchen/.coordination/local-t2-20261013')
W = V / 'worktree'
ROOT = 'Jsp000404.R1DispatchT2'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
GUARD_SHA = 'ad79c57199924e211b0cb41b374216b3f5370d4be95de7f63ee0134e439d0ba2'
MANIFEST_SHA = '60282c6b881335792e80bb0a7df1be42e900a7be96cc36fd5ab49172ca0ccff3'
EMPTY = {'Jsp000404.K3bGeometry', 'Jsp000404.K3bGeometryPart3', 'Jsp000404.S7Defs', 'Jsp000404.DeletionRigidity', 'Jsp000404.R3WitnessDag'}
BASELINE = {
    'Jsp000404.Section4Legality': {'Jsp404.staircase_of_legality'},
    'Jsp000404.Deletion': {'Jsp404.exists_removable_hull_vertex', 'Jsp404.exists_removable_vertex'},
    'Jsp000404.GeometricDeletion': {'Jsp404.maxGap_boundary_emission'},
}
FROZEN = {
    'S7Defs': '6ed0785c4bda102c20b55f0b3697d5ef8efa9ef70c2fb9fd06a0d5ac91b77b2a',
    'S7N7Defs': '107eb58f3c0afb48552a5d8860e0fc6defe93fbf596315e5d6f28b87dd8aca43',
    'S8Defs': 'e00de5bdaac45fbd7a01508d88e8dfd58a5b51e169afde391ff6733297775431',
    'S7N7Core': '2f8c81f790e6356ecb8c5e1edf867dddc247ed3a453c17bda293e7c56b863e93',
    'S8N8Core': '161918200a8930063201f41e1234180442e770684dd372f9102cd9aafd0b1230',
    'S8ScoreArithmetic': '8a617614ccaaf21e39a2cfdb6895aa97ae20a6a49521c13719179157cea2c63d',
}

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def src(m):
    return W / (('ThirdParty/Sendov/' if m.startswith('JSP404.') else '') + m.replace('.', '/') + '.lean')

def olean(m):
    return W / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')

def need(ok, message):
    if not ok:
        raise ValueError(message)

def step(record, expected, context):
    log = Path(record['log'])
    r = json.loads(Path(str(log) + '.json').read_text())
    need(record['accepted'] and r == record['receipt'], 'receipt/record mismatch')
    need(sha(log) == record['log_sha256'], 'log hash mismatch')
    need(record['guard_sha256'] == context['guard'] == GUARD_SHA == sha(V.parent / 'run_jsp_heavy.py'), 'guard mismatch')
    need(r['argv'] == expected and r['cwd'] == str(W), 'command/target mismatch')
    need(r['status'] == 'OK' and r['exit_code'] == r['child_exit'] == 0, 'execution failed')
    need(r['wall_cap_s'] == 180 and r['elapsed_s'] <= 180 and r['nice'] == 15, 'wall/nice mismatch')
    need(r['max_rss_kib'] <= r['rss_cap_gib'] * 1024**2, 'RSS exceeded')
    if r.get('mapped_rss_requested_gib'):
        need(r['mapped_rss_requested_gib'] == 6 and r['rss_cap_gib'] <= 6
             and r['footprint_cap_gib'] == 4 and r['max_footprint_bytes'] is not None
             and r['max_footprint_bytes'] <= 4 * 1024**3 and r['preflight_free_percent'] >= 55
             and r['preflight_free_min_percent'] == 55 and r['running_free_min_percent'] == 45,
             'physical calibration mismatch')
    else:
        need(r['rss_cap_gib'] == 4, 'default RSS cap mismatch')
    text = log.read_text()
    need(not re.search(r'\berror[:(]', text), 'Lean error in log')
    return text

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--partial', action='store_true')
    args = ap.parse_args()
    state_bytes = (V / 'batch_state.json').read_bytes()
    state = json.loads(state_bytes)
    state_sha = hashlib.sha256(state_bytes).hexdigest()
    snapshot = Path('/Users/wizout/op/learn/sunyuchen/.coordination/local-t1-20261015/root_borrow_origin_snapshot.json')
    snapshot.write_bytes(state_bytes)
    context = state['context']
    errors, checked, pending, baselines = [], [], [], []
    audit_logs, seen, active, order, imports = {}, set(), set(), [], {}
    def visit(m):
        if not src(m).exists():
            return
        need(m not in active, 'source import cycle: ' + m)
        if m in seen:
            return
        active.add(m)
        with src(m).open() as f:
            imports[m] = [match[1] for line in f if (match := re.match(r'^import\s+(\S+)', line))]
        for d in imports[m]:
            visit(d)
        active.remove(m)
        seen.add(m)
        order.append(m)
    visit(ROOT)
    manifest = json.loads((V.parent / 't2-quota-recovery-20261013/OVERLAY_MANIFEST.json').read_text())
    omitted = sorted({x['module'] for x in manifest['modules']} - seen)
    if omitted:
        errors.append({'scope': 'original closure', 'omitted': omitted})
    pins = json.loads((V / 'root_source_pins.json').read_text())
    need(set(pins['modules']) == seen, 'pinned source closure changed')
    for m, expected in pins['modules'].items():
        need(sha(src(m)) == expected, 'pinned source changed: ' + m)
    for item in manifest['modules']:
        if item['module'] not in {'Jsp000404.K3bGeometry', 'Jsp000404.ProjectionDescent', 'Jsp000404.DeletionRigidity', 'Jsp000404.R3WitnessDag', 'Jsp000404.R1DispatchT2'}:
            need(sha(src(item['module'])) == item['sha256'], 'original mathematical source changed: ' + item['module'])
    specs = json.loads((W / 'tools/r1_specs.json').read_text())['T2']
    fmap = json.loads((W / 'tools/r1_map.json').read_text())
    required = set()
    for spec in specs.values():
        key = 'T2|' + ','.join(f'{kind}@{rank}' for rank, kind in spec)
        modes = [['H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_IR'] if kind == 's2' else ['L_0', 'L_I', 'L_R'] for _, kind in spec]
        required.update(key + '|' + ','.join(combo) for combo in itertools.product(*modes))
        name = 'R1CertT2_' + '_'.join(f'{kind[1]}{rank}' for rank, kind in spec)
        theorem = 'r1cert_T2_' + '_'.join(f'{kind}a{rank}' for rank, kind in spec)
        need('Jsp000404.' + name in seen and re.search(r'^theorem ' + re.escape(theorem) + r'\b', src('Jsp000404.' + name).read_text(), re.M), 'certificate missing')
    need(len(specs) == 14 and len(required) == 972 and required == {k for k in fmap if k.startswith('T2|')}, 'key/spec coverage changed')
    need(all(not fmap[k].startswith('NONUNSAT') for k in required), 'non-UNSAT key')
    for a, z in itertools.permutations(range(6), 2):
        profile = {a: 's2', **{r: 's1' for r in range(6) if r not in (a, z)}}
        need(any(all(profile.get(rank) == kind for rank, kind in spec) for spec in specs.values()), 'rank assignment uncovered')
    need(len(order) == state['closure_size'], 'live closure size mismatch')
    need(hashlib.sha256(json.dumps(context, sort_keys=True).encode()).hexdigest() == state['context_sha256'], 'context digest mismatch')
    for name, expected in FROZEN.items():
        need(sha(W / 'Jsp000404' / (name + '.lean')) == expected, 'frozen interface changed: ' + name)
    need(sha(W / 'lake-manifest.json') == context['manifest'] and sha(W / 'lakefile.lean') == context['lakefile'], 'project configuration changed')
    need(context['manifest'] == MANIFEST_SHA and context['toolchain'] == 'leanprover/lean4:v4.34.0', 'frozen dependency manifest/toolchain changed')
    manifest_packages = {p['name']: p['rev'] for p in json.loads((W / 'lake-manifest.json').read_text())['packages']}
    need({p['name']: p['rev'] for p in context['packages']} == manifest_packages, 'package context does not cover manifest')
    need((W / 'lean-toolchain').read_text().strip() == context['toolchain'], 'toolchain changed')
    lean = Path(context['lean_path'].split(':')[-1]).parent.parent / 'bin/lean'
    need(sha(lean) == context['lean'], 'Lean binary changed')
    command = [str(lean), '-j1', '-M4096']
    fps = {}
    for m in order:
        x = state['modules'].get(m, {})
        src_hash = sha(src(m))
        dependencies = [(d, fps.get(d), sha(olean(d)) if olean(d).exists() else None) for d in imports[m]]
        fp = hashlib.sha256(json.dumps([src_hash, state['context_sha256'], dependencies]).encode()).hexdigest()
        fps[m] = fp
        if x.get('state') not in {'PASSED', 'AUDITED_NON_STD3'}:
            pending.append(m)
            continue
        try:
            need(x['src_sha256'] == src_hash and x['dep_fp'] == fp and x['ctx'] == state['context_sha256'], 'current source/dependencies mismatch')
            need(sha(olean(m)) == x['olean_sha256'], 'output hash mismatch')
            step(x['normal'], command + ['-o', str(olean(m)), '-i', str(olean(m).with_suffix('.ilean')), str(src(m))], context)
            step(x['strict'], command + ['--trust=0', str(src(m))], context)
            a = state['audits'][x['audit']]
            need(a['srcs'][m] == src_hash and a['dep_fps'][m] == fp and sha(a['probe']) == a['probe_sha256'], 'audit binding mismatch')
            if x['audit'] not in audit_logs:
                audit_logs[x['audit']] = step(a, command + ['--trust=0', a['probe']], context)
            text = audit_logs[x['audit']]
            headers = re.findall(r'AUDITMOD ' + re.escape(m) + r' (\d+)', text)
            rows = re.findall(r'AUDITDECL ' + re.escape(m) + r' (\S+) AXIOMS \[([^\]]*)\]', text)
            need(len(headers) == 1 and int(headers[0]) == len(rows), 'incomplete declaration audit')
            need(bool(rows) or m in EMPTY, 'empty audit not allowed')
            bad = {n for n, ax in rows if not {z.strip() for z in ax.split(',') if z.strip()} <= STD}
            if m in BASELINE:
                need(bad == BASELINE[m] and x['state'] == 'AUDITED_NON_STD3', 'baseline axiom inventory changed')
                baselines.append(m)
            else:
                need(not bad and x['state'] == 'PASSED', 'non-Std3 proof')
                checked.append(m)
        except (OSError, KeyError, ValueError, TypeError) as e:
            errors.append({'module': m, 'error': str(e)})
    terminal = False
    if not args.partial and not pending and not errors:
        # Full completion also requires fresh library context and typed terminal receipts.
        for package in context['packages']:
            folder = W / '.lake/packages' / package['name']
            need(subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD'], text=True).strip() == package['rev'], 'package revision changed')
            need(not subprocess.check_output(['git', '-C', str(folder), 'status', '--porcelain'], text=True), 'package source dirty')
            h = hashlib.sha256()
            root = folder / '.lake/build/lib/lean'
            for f in sorted(root.rglob('*.olean')):
                h.update(str(f.relative_to(root)).encode())
                h.update(sha(f).encode())
            need(h.hexdigest() == package['olean_tree_sha256'], 'package binary tree changed')
        probe = json.loads((V / 'terminal_probe_state.json').read_text())
        p = V / 'probe/TerminalAPI.lean'
        need(probe['probe_sha256'] == sha(p) and probe['terminal_dep_fp'] == fps[ROOT], 'terminal probe source/dependency mismatch')
        for phase in ('normal', 'strict'):
            argv = command + (['--trust=0'] if phase == 'strict' else []) + [str(p)]
            text = step(probe[phase], argv, context)
            for theorem in ('r1_seven_phi21_terminal', 'r1_phi21_unique_defect4'):
                matches = re.findall(r"'Jsp404\." + theorem + r"' depends on axioms: \[([^\]]*)\]", text)
                need(len(matches) == 1 and {z.strip() for z in matches[0].split(',') if z.strip()} <= STD, 'terminal axiom report missing/invalid')
        terminal = True
    report = {'verdict': 'KERNEL_COVERED' if terminal else 'PARTIAL_ONLY', 'state_sha256': state_sha, 'state_snapshot': str(snapshot),
              'closure': len(order), 'verified_std3': len(checked), 'baseline_nonstd3': baselines,
              'pending': pending, 'errors': errors, 'terminal_accepted': terminal,
              'note': 'Baseline admitted declarations are reported separately; terminal must have only Std3.'}
    Path('/Users/wizout/op/learn/sunyuchen/.coordination/local-t1-20261015/root_borrow_origin_acceptance.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('verdict', 'closure', 'verified_std3', 'baseline_nonstd3', 'errors', 'terminal_accepted')}))
    print('pending', len(pending))
    return 0 if not errors and (args.partial or terminal) else 1

if __name__ == '__main__':
    raise SystemExit(main())
