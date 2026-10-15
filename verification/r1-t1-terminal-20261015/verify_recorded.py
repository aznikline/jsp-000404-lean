"""Verify archived T1 receipts against this source checkout, without binary caches.

Stage 1 verifies the sibling T2 evidence pack (the borrow origin).
Stage 2 verifies T1 source pins, borrowed provenance bindings, the 566-module
closure, fresh normal/strict/audit receipts and coverage.

This verifies recorded evidence only. Use reproduce/ to rerun the kernel.
"""
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys

V = Path(__file__).resolve().parent
R = V / 'recorded'
W = V.parents[1]
T2P = V.parent / 'r1-t2-terminal-20261015'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
BASELINE = {
    'Jsp000404.Section4Legality',
    'Jsp000404.Deletion',
    'Jsp000404.GeometricDeletion',
}

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def need(ok, message):
    if not ok:
        raise ValueError(message)

def source(m):
    return W / (('ThirdParty/Sendov/' if m.startswith('JSP404.') else '') + m.replace('.', '/') + '.lean')

def step(x, expected=None):
    p = R / 'logs' / Path(x['log']).name
    receipt = json.loads(Path(str(p) + '.json').read_text())
    need(x['accepted'] and receipt == x['receipt'], 'receipt mismatch: ' + str(p))
    need(x['wrapper_rc'] == 0, 'wrapper failed')
    if expected is not None:
        need(receipt['argv'] == expected, 'recorded compiler command differs')
    need(sha(p) == x['log_sha256'], 'log changed: ' + str(p))
    need(x['guard_sha256'] == sha(V / 'run_jsp_heavy.py'), 'guard changed')
    need(receipt['status'] == 'OK' and receipt['child_exit'] == receipt['exit_code'] == 0, 'unsuccessful execution')
    need(receipt['argv'][1:3] == ['-j1', '-M4096'] and receipt['nice'] == 15, 'compiler resource settings changed')
    need(receipt['wall_cap_s'] == 180 and receipt['elapsed_s'] <= 180, 'wall limit exceeded')
    need(receipt['rss_cap_gib'] == 4 and not receipt.get('mapped_rss_requested_gib'), 'T1 lane must use default RSS4')
    need(receipt['max_rss_kib'] <= receipt['rss_cap_gib'] * 1024**2, 'RSS limit exceeded')
    text = p.read_text()
    need(not re.search(r'\berror[:(]', text), 'Lean error in accepted log')
    return text, receipt['argv']

def stage_t2():
    v = T2P / 'verify_recorded.py'
    need(v.exists(), 'sibling T2 evidence pack missing: ' + str(T2P))
    r = subprocess.run([sys.executable, str(v)], capture_output=True, text=True)
    sys.stdout.write(r.stdout); sys.stderr.write(r.stderr)
    need(r.returncode == 0, 'T2 archived evidence verification failed')

def main():
    stage_t2()
    report = json.loads((R / 'root_t1_acceptance.json').read_text())
    snapshot = R / 'root_state_snapshot.json'
    need(sha(snapshot) == report['state_sha256'], 'recorded state snapshot changed')
    need(not report['errors'] and not report['pending'], 'unresolved module errors/pending')
    terminal_ok = report['verdict'] == 'KERNEL_COVERED' and report['terminal_accepted']
    s = json.loads(snapshot.read_text())
    historical_worktree = s['modules']['Jsp000404.R1DispatchT1']['normal']['receipt']['cwd']
    compiler = str(Path(s['context']['lean_path'].split(':')[-1]).parent.parent / 'bin/lean')
    command = [compiler, '-j1', '-M4096']
    pins = json.loads((R / 'root_input_acceptance.json').read_text())['modules']
    origin_snap = R / 'root_borrow_origin_snapshot.json'
    need(sha(origin_snap) == sha(T2P / 'recorded/root_state_snapshot.json'),
         'origin snapshot not byte-bound to committed T2 evidence')
    origin = json.loads(origin_snap.read_text())['modules']
    borrowed = set(json.loads((R / 'root_input_acceptance.json').read_text())['borrowed_modules'])
    need(len(pins) == report['closure'] == s['closure_size'] == 566, 'closure size changed')
    need(hashlib.sha256(json.dumps(s['context'], sort_keys=True).encode()).hexdigest()
         == s['context_sha256'], 'recorded context digest changed')
    need(sha(W / 'lake-manifest.json') == s['context']['manifest'], 'dependency manifest changed')
    need(sha(W / 'lakefile.lean') == s['context']['lakefile'], 'Lake project changed')
    audit_texts, inherited, baseline, fresh, visited, active = {}, [], [], [], set(), set()
    order, fingerprints = [], {}
    def visit(m):
        need(m not in active, 'import cycle')
        if m in visited:
            return
        need(m in pins, 'project module omitted: ' + m)
        active.add(m)
        text = source(m).read_text()
        for dep in re.findall(r'^import\s+(\S+)', text, re.M):
            if dep.startswith(('Jsp000404.', 'JSP404.')):
                visit(dep)
        active.remove(m)
        visited.add(m)
        order.append(m)
    visit('Jsp000404.R1DispatchT1')
    need(visited == set(pins), 'source import closure differs from evidence')
    need(len(visited - borrowed) == 22, 'fresh module count differs')
    for m in order:
        x = s['modules'][m]
        need(sha(source(m)) == pins[m] == x['src_sha256'], 'source changed: ' + m)
        if m in borrowed:
            old = origin[m]
            need(old['src_sha256'] == pins[m], 'borrowed origin source differs from pin: ' + m)
            expected = 'BORROWED_NON_STD3' if old['state'] == 'AUDITED_NON_STD3' else 'BORROWED'
            need(x['state'] == expected, 'borrowed state upgraded: ' + m)
            need(all(d in borrowed for d in re.findall(r'^import\s+(\S+)', source(m).read_text(), re.M)
                     if d in pins), 'borrowed dependency changed: ' + m)
            prov = x['borrowed_from']
            for k in ('ctx', 'dep_fp', 'audit', 'olean_sha256'):
                need(prov[k] == old[k], 'borrowed provenance differs: ' + m + '/' + k)
            need(x['olean_sha256'] == old['olean_sha256'], 'borrowed output binding differs')
            fingerprints[m] = old['olean_sha256']
            out = W / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
            if out.exists():
                need(sha(out) == prov['olean_sha256'], 'borrowed artifact changed: ' + m)
            (baseline if expected == 'BORROWED_NON_STD3' else inherited).append(m)
            continue
        dependencies = [(d, fingerprints.get(d), s['modules'].get(d, {}).get('olean_sha256'))
                        for d in re.findall(r'^import\s+(\S+)', source(m).read_text(), re.M)]
        fingerprints[m] = hashlib.sha256(json.dumps([pins[m], s['context_sha256'], dependencies]).encode()).hexdigest()
        need(x['ctx'] == s['context_sha256'] and x['dep_fp'] == fingerprints[m],
             'fresh transitive dependency fingerprint differs: ' + m)
        relative = ('ThirdParty/Sendov/' if m.startswith('JSP404.') else '') + m.replace('.', '/')
        historical_source = str(Path(historical_worktree) / (relative + '.lean'))
        historical_output = Path(historical_worktree) / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
        for phase in ('normal', 'strict'):
            expected = command + (['--trust=0', historical_source] if phase == 'strict' else
                                  ['-o', str(historical_output), '-i', str(historical_output.with_suffix('.ilean')), historical_source])
            _, argv = step(x[phase], expected)
            need(x[phase]['receipt']['cwd'] == historical_worktree, 'recorded cwd differs')
            need(argv[-1].endswith(m.replace('.', '/') + '.lean'), 'compiler source target differs')
            need(('--trust=0' in argv) == (phase == 'strict'), 'strict phase missing')
        need(x['state'] == 'PASSED', 'fresh module not passed: ' + m)
        a = s['audits'][x['audit']]
        need(a['srcs'][m] == pins[m] and a['dep_fps'][m] == x['dep_fp'], 'audit binding differs')
        need(sha(R / 'probe' / Path(a['probe']).name) == a['probe_sha256'], 'audit probe changed')
        if x['audit'] not in audit_texts:
            audit_texts[x['audit']] = step(a, command + ['--trust=0', a['probe']])[0]
            need(a['receipt']['cwd'] == historical_worktree, 'audit cwd differs')
        text = audit_texts[x['audit']]
        heads = re.findall(r'AUDITMOD ' + re.escape(m) + r' (\d+)', text)
        rows = re.findall(r'AUDITDECL ' + re.escape(m) + r' (\S+) AXIOMS \[([^\]]*)\]', text)
        need(len(heads) == 1 and int(heads[0]) == len(rows) and rows, 'incomplete fresh audit: ' + m)
        bad = {n for n, ax in rows if not {a.strip() for a in ax.split(',') if a.strip()} <= STD}
        need(not bad, 'fresh non-Std3 declaration: ' + m)
        fresh.append(m)
    need(len(inherited) == 541 and len(baseline) == 3 and len(fresh) == 22, 'module counts differ')
    dispatch = (W / 'Jsp000404/R1DispatchT1.lean').read_text()
    rmap = json.loads((R / 'r1_map.json').read_text())
    live = W / 'tools/r1_map.json'
    need(not live.exists() or sha(live) == sha(R / 'r1_map.json'), 'live key map changed')
    t1keys = [k for k in rmap if k.startswith('T1|')]
    spec_groups = {k.split('|')[1] for k in t1keys}
    need(len(t1keys) == 180 and len(spec_groups) == 6, 'recomputed key/spec count differs')
    need(all(rmap[k].startswith('P6|') for k in t1keys), 'non-UNSAT T1 key found')
    specs = json.loads((R / 'r1_specs.json').read_text())['T1']
    live_specs = W / 'tools/r1_specs.json'
    need(not live_specs.exists() or sha(live_specs) == sha(R / 'r1_specs.json'), 'live spec table changed')
    need(len(specs) == 6 and all(sum(kind == 's2' for _, kind in rows) == 1
         and len({rank for rank, _ in rows}) == len(rows)
         and all(rank in range(6) and kind in {'s1', 's2'} for rank, kind in rows)
         for rows in specs.values()), 'spec table changed')
    required = set()
    for rows in specs.values():
        stem = 'T1|' + ','.join(f'{kind}@{rank}' for rank, kind in rows)
        modes = [('H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_IR') if kind == 's2'
                 else ('L_0', 'L_I', 'L_R') for _, kind in rows]
        required.update(stem + '|' + ','.join(c) for c in itertools.product(*modes))
    need(len(required) == 180 and required == set(t1keys), 'canonical key identities incomplete')
    need(sum(1 for v in specs.values() for x in v if x[1] == 's2') == 6
         and len({x[0] for v in specs.values() for x in v if x[1] == 's2'}) == 6,
         's2-rank coverage differs')
    ncerts = len(re.findall(r'^import Jsp000404\.R1CertT1_', dispatch, re.M))
    need(ncerts == 6, 'certificate import coverage differs')
    need(len(re.findall(r'theorem r1t1_u\d ', dispatch)) == 6, 'spec helpers changed')
    need(len(re.findall(r'exact r1t1_u\d ', dispatch)) == 6, 'spec call sites changed')
    need(dispatch.count('fin_cases ra') == 1, 'rank dispatch changed')
    ledger = json.loads((R / 'root_dispatch_statement_ledger.json').read_text())
    need(ledger['theorem_count'] == 8 and ledger['all_statements_identical'], 'original statements changed')
    pin = json.loads((R / 'root_probe_pin.json').read_text())
    need(sha(R / 'probe' / 'TerminalAPI.lean') == pin['probe_sha256'], 'original API probe changed')
    tps = R / 'root_terminal_probe_state.json'
    if tps.exists():
        probe = json.loads(tps.read_text())
        need(probe['probe_sha256'] == pin['probe_sha256']
             and probe['terminal_dep_fp'] == s['modules']['Jsp000404.R1DispatchT1']['dep_fp']
             and probe['context_sha256'] == s['context_sha256'], 'terminal probe binding differs')
        for phase in ('normal', 'strict'):
            probe_target = probe['normal']['receipt']['argv'][-1]
            text, _ = step(probe[phase], command + (['--trust=0'] if phase == 'strict' else []) + [probe_target])
            need(probe[phase]['receipt']['cwd'] == historical_worktree, 'original API cwd differs')
            for name in ('r1_seven_phi22_terminal', 'r1_phi22_all_defect3'):
                ax = re.findall(r"'Jsp404\." + name + r"' depends on axioms: \[([^\]]*)\]", text)
                need(len(ax) == 1 and {a.strip() for a in ax[0].split(',') if a.strip()} <= STD,
                     'terminal axiom closure differs')
        need(terminal_ok, 'Root final acceptance inconsistent with probe evidence')
        print('KERNEL_COVERED: 566 modules; 541 borrowed Std3 + 3 baseline + 22 fresh Std3; terminal Std3.')
    else:
        print('PENDING_ROOT_TERMINAL_PROBE: module evidence verified but terminal probe/acceptance absent.', file=sys.stderr)
        print('This is NOT a successful verification.', file=sys.stderr)
        raise SystemExit(1)
    print('This checks archived evidence. Run reproduce/ to execute fresh kernel verification.')

if __name__ == '__main__':
    main()
