"""Verify archived receipts against this source checkout, without binary caches.

This verifies recorded evidence. Use reproduce/ to rerun the Lean kernel.
"""
import hashlib
import json
from pathlib import Path
import re

V = Path(__file__).resolve().parent
R = V / 'recorded'
W = V.parents[1]
STD = {'propext', 'Classical.choice', 'Quot.sound'}
EMPTY = {'Jsp000404.K3bGeometry', 'Jsp000404.K3bGeometryPart3', 'Jsp000404.S7Defs', 'Jsp000404.DeletionRigidity', 'Jsp000404.R3WitnessDag'}
BASELINE = {
    'Jsp000404.Section4Legality': {'Jsp404.staircase_of_legality'},
    'Jsp000404.Deletion': {'Jsp404.exists_removable_hull_vertex', 'Jsp404.exists_removable_vertex'},
    'Jsp000404.GeometricDeletion': {'Jsp404.maxGap_boundary_emission'},
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

def step(x):
    p = R / 'logs' / Path(x['log']).name
    receipt = json.loads(Path(str(p) + '.json').read_text())
    need(x['accepted'] and receipt == x['receipt'], 'receipt mismatch: ' + str(p))
    need(sha(p) == x['log_sha256'], 'log changed: ' + str(p))
    need(x['guard_sha256'] == sha(V / 'run_jsp_heavy.py'), 'guard changed')
    need(receipt['status'] == 'OK' and receipt['child_exit'] == receipt['exit_code'] == 0, 'unsuccessful execution')
    need(receipt['argv'][1:3] == ['-j1', '-M4096'] and receipt['nice'] == 15, 'compiler resource settings changed')
    need(receipt['wall_cap_s'] == 180 and receipt['elapsed_s'] <= 180, 'wall limit exceeded')
    need(receipt['max_rss_kib'] <= receipt['rss_cap_gib'] * 1024**2, 'RSS limit exceeded')
    if receipt.get('mapped_rss_requested_gib'):
        need(receipt['mapped_rss_requested_gib'] == 6 and receipt['rss_cap_gib'] <= 6
             and receipt['footprint_cap_gib'] == 4 and receipt['max_footprint_bytes'] <= 4 * 1024**3
             and receipt['preflight_free_percent'] >= 55 and receipt['running_free_min_percent'] == 45,
             'mapped-memory calibration invalid')
    else:
        need(receipt['rss_cap_gib'] == 4, 'default RSS limit changed')
    text = p.read_text()
    need(not re.search(r'\berror[:(]', text), 'Lean error in accepted log')
    return text, receipt['argv']

def main():
    report = json.loads((R / 'root_local_acceptance.json').read_text())
    snapshot = R / 'root_state_snapshot.json'
    need(sha(snapshot) == report['state_sha256'], 'recorded state snapshot changed')
    need(report['verdict'] == 'KERNEL_COVERED' and report['terminal_accepted'] and not report['errors'] and not report['pending'], 'original full acceptance missing')
    s = json.loads(snapshot.read_text())
    pins = json.loads((R / 'root_source_pins.json').read_text())['modules']
    need(len(pins) == report['closure'] == s['closure_size'], 'closure size changed')
    need(hashlib.sha256(json.dumps(s['context'], sort_keys=True).encode()).hexdigest() == s['context_sha256'], 'recorded context digest changed')
    for m, expected in pins.items():
        need(sha(source(m)) == expected == s['modules'][m]['src_sha256'], 'source changed: ' + m)
    need(sha(W / 'lake-manifest.json') == s['context']['manifest'], 'dependency manifest changed')
    need(sha(W / 'lakefile.lean') == s['context']['lakefile'], 'Lake project changed')
    audit_texts, verified, baseline, visited, active = {}, [], [], set(), set()
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
    visit('Jsp000404.R1DispatchT2')
    need(visited == set(pins), 'source import closure differs from evidence')
    for m in pins:
        x = s['modules'][m]
        for phase in ('normal', 'strict'):
            _, argv = step(x[phase])
            need(argv[-1].endswith(m.replace('.', '/') + '.lean'), 'compiler source target differs')
            need(('--trust=0' in argv) == (phase == 'strict'), 'strict phase missing')
        a = s['audits'][x['audit']]
        need(a['srcs'][m] == pins[m] and a['dep_fps'][m] == x['dep_fp'], 'audit binding differs')
        need(sha(R / 'probe' / Path(a['probe']).name) == a['probe_sha256'], 'audit source changed')
        if x['audit'] not in audit_texts:
            audit_texts[x['audit']] = step(a)[0]
        text = audit_texts[x['audit']]
        headers = re.findall(r'AUDITMOD ' + re.escape(m) + r' (\d+)', text)
        rows = re.findall(r'AUDITDECL ' + re.escape(m) + r' (\S+) AXIOMS \[([^\]]*)\]', text)
        need(len(headers) == 1 and int(headers[0]) == len(rows), 'incomplete axiom audit: ' + m)
        need(bool(rows) or m in EMPTY, 'unexpected empty declaration audit: ' + m)
        bad = {n for n, ax in rows if not {a.strip() for a in ax.split(',') if a.strip()} <= STD}
        if m in BASELINE:
            need(bad == BASELINE[m] and x['state'] == 'AUDITED_NON_STD3', 'baseline admission inventory differs')
            baseline.append(m)
        else:
            need(not bad and x['state'] == 'PASSED', 'non-Std3 declaration: ' + m)
            verified.append(m)
    probe = json.loads((R / 'terminal_probe_state.json').read_text())
    need(sha(R / 'probe/TerminalAPI.lean') == probe['probe_sha256'], 'original API probe changed')
    need(probe['terminal_dep_fp'] == s['modules']['Jsp000404.R1DispatchT2']['dep_fp'], 'terminal dependency binding differs')
    for phase in ('normal', 'strict'):
        text, argv = step(probe[phase])
        need(('--trust=0' in argv) == (phase == 'strict'), 'terminal strict phase missing')
        for name in ('r1_seven_phi21_terminal', 'r1_phi21_unique_defect4'):
            ax = re.findall(r"'Jsp404\." + name + r"' depends on axioms: \[([^\]]*)\]", text)
            need(len(ax) == 1 and {a.strip() for a in ax[0].split(',') if a.strip()} <= STD, 'terminal axiom closure differs')
    need(len(verified) == report['verified_std3'] and len(baseline) == 3, 'module counts differ')
    print(f'RECORDED_RECEIPTS_VERIFIED: {len(pins)} modules; {len(verified)} Std3; 3 baseline modules separately reported; original-API normal/strict terminal evidence intact.')
    print('This checks archived evidence. Run reproduce/ to execute fresh kernel verification.')

if __name__ == '__main__':
    main()
