"""Root's independent T1 source and borrowed-evidence boundary check (no Lean)."""
import hashlib
import itertools
import json
from pathlib import Path
import re

V = Path(__file__).resolve().parent
B = V.parent
W = V / 'worktree'
OLD = B / 'local-t2-20261013'
PACKAGE = B / 't1-input/package'
ROOT = 'Jsp000404.R1DispatchT1'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def need(ok, message):
    if not ok:
        raise ValueError(message)

def source(w, module):
    return w / (('ThirdParty/Sendov/' if module.startswith('JSP404.') else '')
                + module.replace('.', '/') + '.lean')

def signatures(text):
    return re.findall(r'^theorem\s+.*?(?=\s*:=)', text, re.M | re.S)

def same_signature(before, after):
    need(signatures(before) == signatures(after), 'original theorem signature changed')

def main():
    origin_path = V / 'root_borrow_origin_acceptance.json'
    origin = json.loads(origin_path.read_text())
    snapshot = V / 'root_borrow_origin_snapshot.json'
    need(origin['verdict'] == 'KERNEL_COVERED' and origin['terminal_accepted']
         and not origin['errors'] and not origin['pending'], 'old evidence not accepted')
    need(sha(snapshot) == origin['state_sha256'], 'origin snapshot changed')
    old = json.loads(snapshot.read_text())
    overlay = json.loads((V / 'input-overlay.json').read_text())
    need(sha(PACKAGE / 'source-manifest.json') == overlay['package_manifest_sha256'],
         'original package manifest changed')
    manifest = json.loads((PACKAGE / 'source-manifest.json').read_text())
    need(len(manifest['files']) == 485, 'package scope changed')
    files = {x['module']: x for x in manifest['files']}
    for module, item in files.items():
        need(sha(PACKAGE / item['file']) == item['sha256'], 'package source changed: ' + module)
        live = source(W, module)
        if module.startswith('Jsp000404.R1LeavesN7_'):
            need(sha(live) == item['sha256'], 'leaf mathematical source changed: ' + module)
        else:
            same_signature((PACKAGE / item['file']).read_text(), live.read_text())

    imports, order, active = {}, [], set()
    def visit(module):
        p = source(W, module)
        if not p.exists():
            need(not module.startswith(('Jsp000404.', 'JSP404.')), 'missing project source: ' + module)
            return
        need(module not in active, 'import cycle: ' + module)
        if module in imports:
            return
        active.add(module)
        imports[module] = re.findall(r'^import\s+(\S+)', p.read_text(), re.M)
        for dep in imports[module]:
            visit(dep)
        active.remove(module)
        order.append(module)
    visit(ROOT)
    need(set(files) <= set(order), 'original package modules omitted from closure')
    borrowed, fresh = [], []
    for module in order:
        live = source(W, module)
        rec = old['modules'].get(module)
        if rec and sha(live) == rec['src_sha256'] and all(d not in fresh for d in imports[module]):
            need(rec['state'] in {'PASSED', 'AUDITED_NON_STD3'}, 'unaccepted origin module')
            out = OLD / 'worktree/.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
            need(sha(out) == rec['olean_sha256'], 'borrowed output changed: ' + module)
            need(sha(source(OLD / 'worktree', module)) == rec['src_sha256'], 'origin source changed')
            borrowed.append(module)
        else:
            need(module in files or module.startswith('Jsp000404.R1T1'),
                 'unapproved changed dependency: ' + module)
            fresh.append(module)
    specs = json.loads((W / 'tools/r1_specs.json').read_text())['T1']
    fmap = json.loads((W / 'tools/r1_map.json').read_text())
    required = set()
    for spec in specs.values():
        stem = 'T1|' + ','.join(f'{kind}@{rank}' for rank, kind in spec)
        modes = [('H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_IR') if kind == 's2'
                 else ('L_0', 'L_I', 'L_R') for _, kind in spec]
        required.update(stem + '|' + ','.join(c) for c in itertools.product(*modes))
        module = 'Jsp000404.R1CertT1_' + '_'.join(f'{kind[1]}{rank}' for rank, kind in spec)
        need(module in imports, 'original certificate missing')
    need(len(specs) == 6 and len(required) == 180
         and required == {k for k in fmap if k.startswith('T1|')}, 'key/spec scope changed')
    need(all(not fmap[k].startswith('NONUNSAT') for k in required), 'unresolved key')
    for rank in range(6):
        profile = {r: ('s2' if r == rank else 's1') for r in range(6)}
        need(any(all(profile[r] == kind for r, kind in s) for s in specs.values()), 'rank uncovered')
    for name in ('lake-manifest.json', 'lakefile.lean', 'lean-toolchain'):
        need(sha(W / name) == sha(OLD / 'worktree' / name), 'configuration changed: ' + name)
    need((W / '.lake/packages').resolve() == (OLD / 'worktree/.lake/packages').resolve(),
         'borrowed library path changed')
    need(sha(B / 'run_jsp_heavy.py') == old['context']['guard'], 'guard changed')
    report = dict(verdict='SOURCE_AND_BORROW_BOUNDARY_VERIFIED', kernel_terminal_accepted=False,
                  closure=len(order), borrowed=len(borrowed), fresh=len(fresh), keys=len(required),
                  specs=len(specs), ranks=6, origin_report_sha256=sha(origin_path),
                  origin_state_sha256=sha(snapshot), modules={m: sha(source(W, m)) for m in order},
                  borrowed_modules=borrowed, fresh_modules=fresh,
                  note='Fresh proof acceptance requires normal, trust=0, Std3 audits and typed original API probe.')
    (V / 'root_input_acceptance.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('verdict', 'closure', 'borrowed', 'fresh', 'keys', 'specs', 'ranks')}))

if __name__ == '__main__':
    main()
