"""Independent T1 kernel acceptance: retained T2 evidence + fresh guarded runs."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

V = Path(__file__).resolve().parent
W = V / 'worktree'
OLD = V.parent / 'local-t2-20261013'
ROOT = 'Jsp000404.R1DispatchT1'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
spec = importlib.util.spec_from_file_location('retained_raw_verifier', OLD / 'check_local_t2.py')
raw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(raw)
raw.V, raw.W = V, W

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def need(ok, text):
    if not ok:
        raise ValueError(text)

def source(m):
    return W / (('ThirdParty/Sendov/' if m.startswith('JSP404.') else '') + m.replace('.', '/') + '.lean')

def artifact(m):
    return W / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')

def step(record, argv, context):
    text = raw.step(record, argv, context)
    need(record['wrapper_rc'] == 0, 'wrapper did not exit successfully')
    need(record['receipt']['rss_cap_gib'] == 4 and not record['receipt'].get('mapped_rss_requested_gib'),
         'new T1 runs must use original default RSS4')
    return text

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--partial', action='store_true')
    args = ap.parse_args()
    pins = json.loads((V / 'root_input_acceptance.json').read_text())
    origin = json.loads((V / 'root_borrow_origin_acceptance.json').read_text())
    need(sha(V / 'root_borrow_origin_acceptance.json') == pins['origin_report_sha256'], 'origin report changed')
    need(sha(V / 'root_borrow_origin_snapshot.json') == pins['origin_state_sha256'] == origin['state_sha256'],
         'origin state changed')
    need(origin['terminal_accepted'] and origin['verdict'] == 'KERNEL_COVERED'
         and not origin['errors'] and not origin['pending'], 'original evidence not accepted')
    old = json.loads((V / 'root_borrow_origin_snapshot.json').read_text())
    state_bytes = (V / 'batch_state.json').read_bytes()
    state = json.loads(state_bytes)
    (V / 'root_t1_state_snapshot.json').write_bytes(state_bytes)
    context = state['context']
    ctx = hashlib.sha256(json.dumps(context, sort_keys=True).encode()).hexdigest()
    need(ctx == state['context_sha256'], 'new context digest mismatch')
    for key in ('toolchain', 'lakefile', 'manifest', 'lean', 'guard', 'packages'):
        need(context[key] == old['context'][key], 'borrowed environment mismatch: ' + key)
    for path, key in [('lake-manifest.json', 'manifest'), ('lakefile.lean', 'lakefile')]:
        need(sha(W / path) == context[key], 'project configuration changed')
    need((W / 'lean-toolchain').read_text().strip() == context['toolchain'], 'toolchain changed')
    lean = Path(context['lean_path'].split(':')[-1]).parent.parent / 'bin/lean'
    need(sha(lean) == context['lean'], 'compiler changed')
    package_dirs = sorted((W / '.lake/packages').glob('*/.lake/build/lib/lean'))
    expected_lean_path = ':'.join(str(p.resolve()) for p in package_dirs) + ':' + str(W / '.lake/build/lib/lean') + ':' + str(lean.parent.parent / 'lib/lean')
    need(context['lean_path'] == expected_lean_path, 'unapproved compiler search path')
    cmd = [str(lean), '-j1', '-M4096']
    order, imports, active = [], {}, set()
    def visit(m):
        p = source(m)
        if not p.exists():
            need(not m.startswith(('Jsp000404.', 'JSP404.')), 'missing project import: ' + m)
            return
        need(m not in active, 'import cycle')
        if m in imports:
            return
        active.add(m)
        imports[m] = re.findall(r'^import\s+(\S+)', p.read_text(), re.M)
        for dep in imports[m]:
            visit(dep)
        active.remove(m)
        order.append(m)
    visit(ROOT)
    need(set(order) == set(pins['modules']) and len(order) == state['closure_size'], 'pinned closure changed')
    borrowed = set(pins['borrowed_modules'])
    checked, inherited, baseline, pending, errors, fp, audits = [], [], [], [], [], {}, {}
    for m in order:
        try:
            h = sha(source(m))
            need(h == pins['modules'][m], 'Root approved source pin changed')
            rec = state['modules'].get(m, {})
            if m in borrowed:
                oldrec = old['modules'][m]
                expected = 'BORROWED_NON_STD3' if oldrec['state'] == 'AUDITED_NON_STD3' else 'BORROWED'
                need(rec['state'] == expected and rec['src_sha256'] == h == oldrec['src_sha256'], 'invalid borrowed source/state')
                need(all(d in borrowed for d in imports[m] if d in imports), 'borrowed dependency changed')
                oldout = OLD / 'worktree/.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
                need(sha(oldout) == sha(artifact(m)) == rec['olean_sha256'] == oldrec['olean_sha256'], 'borrowed artifact mismatch')
                need(sha(OLD / 'worktree' / source(m).relative_to(W)) == h, 'old source changed')
                provenance = rec['borrowed_from']
                for key in ('ctx', 'dep_fp', 'audit', 'olean_sha256'):
                    need(provenance[key] == oldrec[key], 'borrowed provenance mismatch: ' + key)
                fp[m] = oldrec['olean_sha256']
                (baseline if expected == 'BORROWED_NON_STD3' else inherited).append(m)
                continue
            deps = [(d, fp.get(d), sha(artifact(d)) if artifact(d).exists() else None) for d in imports[m]]
            fp[m] = hashlib.sha256(json.dumps([h, ctx, deps]).encode()).hexdigest()
            if rec.get('state') != 'PASSED':
                pending.append(m)
                continue
            need(rec['src_sha256'] == h and rec['ctx'] == ctx and rec['dep_fp'] == fp[m], 'fresh source/dependency mismatch')
            need(sha(artifact(m)) == rec['olean_sha256'], 'fresh artifact mismatch')
            step(rec['normal'], cmd + ['-o', str(artifact(m)), '-i', str(artifact(m).with_suffix('.ilean')), str(source(m))], context)
            step(rec['strict'], cmd + ['--trust=0', str(source(m))], context)
            a = state['audits'][rec['audit']]
            need(a['srcs'][m] == h and a['dep_fps'][m] == fp[m] and sha(a['probe']) == a['probe_sha256'], 'fresh audit binding mismatch')
            if rec['audit'] not in audits:
                audits[rec['audit']] = step(a, cmd + ['--trust=0', a['probe']], context)
            text = audits[rec['audit']]
            heads = re.findall(r'AUDITMOD ' + re.escape(m) + r' (\d+)', text)
            rows = re.findall(r'AUDITDECL ' + re.escape(m) + r' (\S+) AXIOMS \[([^\]]*)\]', text)
            need(len(heads) == 1 and int(heads[0]) == len(rows) and rows, 'incomplete or empty fresh audit')
            need(all({x.strip() for x in ax.split(',') if x.strip()} <= STD for _, ax in rows), 'fresh non-Std3 declaration')
            checked.append(m)
        except (KeyError, ValueError, OSError, TypeError) as e:
            errors.append({'module': m, 'error': str(e)})
    terminal = False
    if not args.partial and not pending and not errors:
        need(not state.get('current') and not state.get('stopped'), 'kernel batch is unfinished')
        for p in context['packages']:
            folder = W / '.lake/packages' / p['name']
            need(subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD'], text=True).strip() == p['rev'], 'package revision changed')
            need(not subprocess.check_output(['git', '-C', str(folder), 'status', '--porcelain'], text=True), 'package source dirty')
            tree = hashlib.sha256()
            root = folder / '.lake/build/lib/lean'
            for f in sorted(root.rglob('*.olean')):
                tree.update(str(f.relative_to(root)).encode())
                tree.update(sha(f).encode())
            need(tree.hexdigest() == p['olean_tree_sha256'], 'package output tree changed')
        probe = json.loads((V / 'root_terminal_probe_state.json').read_text())
        p = V / 'probe/TerminalAPI.lean'
        pin = json.loads((V / 'root_probe_pin.json').read_text())
        need(probe['probe_sha256'] == sha(p) == pin['probe_sha256'] and probe['terminal_dep_fp'] == fp[ROOT]
             and probe['context_sha256'] == ctx, 'original API probe binding mismatch')
        for phase in ('normal', 'strict'):
            text = step(probe[phase], cmd + (['--trust=0'] if phase == 'strict' else []) + [str(p)], context)
            for theorem in ('r1_seven_phi22_terminal', 'r1_phi22_all_defect3'):
                ax = re.findall(r"'Jsp404\." + theorem + r"' depends on axioms: \[([^\]]*)\]", text)
                need(len(ax) == 1 and {x.strip() for x in ax[0].split(',') if x.strip()} <= STD, 'original API axiom closure invalid')
        terminal = True
    report = dict(verdict='KERNEL_COVERED' if terminal else 'PARTIAL_ONLY', terminal_accepted=terminal,
                  state_sha256=hashlib.sha256(state_bytes).hexdigest(), closure=len(order),
                  borrowed_std3=len(inherited), baseline_nonstd3=baseline, fresh_std3=len(checked),
                  pending=pending, errors=errors, origin_state_sha256=pins['origin_state_sha256'])
    (V / 'root_t1_acceptance.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))
    return 0 if not errors and (args.partial or terminal) else 1

if __name__ == '__main__':
    raise SystemExit(main())
