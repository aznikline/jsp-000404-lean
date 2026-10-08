#!/usr/bin/env python3
"""Deterministic SOURCE_ONLY subdivision; no search, solver, or Lean."""
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT/'verification/oct8-seven-lower-fixed-cut-source/manifest.json'
EXPECTED = 'd8771fafcb6aa37792e2b29d68174cc576bda1a75faac95fe76f779af9b0a998'
VECTOR = lambda xs: '!['+', '.join(xs)+']'


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    assert digest(INPUT) == EXPECTED and not args.out.exists()
    data = json.loads(INPUT.read_text()); states = data['states']
    originals = {item['module']: item for item in data['modules']}
    pieces, wrappers, before, mapping = {}, {}, {}, []
    for group, values in enumerate(data['groups']):
        if group == 0: continue
        namespace = f'SevenLowerFixedCutGroup{group:02d}'
        original = originals['Jsp000404.'+namespace]
        path = ROOT/original['source']
        assert digest(path) == original['sha256']
        before[path] = path.read_bytes()
        parts, current, work = [], [], 0
        for state in values:
            cost = states[state]['subtree_occurrences']; assert cost <= 256
            if current and work+cost > 256: parts.append((current, work)); current, work = [], 0
            current.append(state); work += cost
        if current: parts.append((current, work))
        modules, references = [], {}
        for part, (selected, work) in enumerate(parts):
            name = f'{namespace}Part{part:02d}'; module = 'Jsp000404.'+name
            modules.append(module)
            text = '\n'.join(['import Jsp000404.SevenLowerFixedCutContexts', '',
                '/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/',
                'set_option autoImplicit false', 'set_option Elab.async false',
                'set_option maxRecDepth 32768', 'set_option maxHeartbeats 0', '',
                'namespace Jsp404.'+name, 'open SevenLowerReplay', ''])
            count = len(selected)
            text += f'def contexts : Fin {count} → Context := '+VECTOR([f'SevenLowerFixedCutContexts.context{s:03d}' for s in selected])+'\n'
            text += f'def fuels : Fin {count} → ℕ := '+VECTOR([str(states[s]['fuel']) for s in selected])+'\n'
            text += f'def ids : Fin {count} → ℕ := '+VECTOR([str(states[s]['node']) for s in selected])+'\n\n'
            text += f'theorem cuts_checked : ∀ j : Fin {count},\n    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide\n\n#print axioms cuts_checked\nend Jsp404.{name}\n'
            pieces[ROOT/'Jsp000404'/f'{name}.lean'] = text
            mapping.append({'module': module, 'group': group, 'part': part, 'states': selected,
                            'work': work, 'selected': ['Jsp404.'+name+'.cuts_checked']})
            for local, state in enumerate(selected): references[state] = (name, local)
        old = before[path].decode()
        assert old.count(':= by decide') == 1
        imports = '\n'.join('import '+module for module in modules)+'\nimport Mathlib.Tactic.FinCases\n'
        body = ':= by\n  intro j\n  fin_cases j\n'+''.join(
            f'  · exact {references[state][0]}.cuts_checked {references[state][1]}\n' for state in values)
        wrappers[path] = imports+old.replace(':= by decide', body.rstrip())
        # Exact original mathematical statement and all three original data
        # definitions are retained; only imports and proof body change.
        assert old.split(':= by decide')[0] in wrappers[path]
    assert len(pieces) == 63 and len(wrappers) == 13 and sum(len(x['states']) for x in mapping) == 235
    assert all(not path.exists() for path in pieces)
    args.out.mkdir(parents=True)
    initial = args.out/'initial-unpassed-groups'; initial.mkdir()
    for path, raw in before.items(): (initial/path.name).write_bytes(raw)
    (args.out/'initial-cut-manifest.json').write_bytes(INPUT.read_bytes())
    (args.out/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    manifest = {'status': 'SOURCE_ONLY_NOT_KERNEL_CHECKED', 'initial_manifest_sha256': EXPECTED,
                'emitter_sha256': digest(Path(__file__)), 'max_total_piece_work': 256,
                'pieces': mapping, 'modules': [], 'wrappers': [], 'solver_runs': 0,
                'Lean_runs': 0, 'search_runs': 0,
                'history': 'Group01 original718fb TIME_CAP; all13 original candidate bytes copied before replacement. Group00/Contexts/ComposedRoot are unchanged.'}
    for path, text in pieces.items():
        path.write_text(text)
        manifest['modules'].append({'module': 'Jsp000404.'+path.stem, 'source': str(path.relative_to(ROOT)),
            'sha256': digest(path), 'bytes': path.stat().st_size, 'selected': ['Jsp404.'+path.stem+'.cuts_checked']})
    for path, text in wrappers.items():
        path.write_text(text)
        manifest['wrappers'].append({'module': 'Jsp000404.'+path.stem, 'source': str(path.relative_to(ROOT)),
            'initial_sha256': hashlib.sha256(before[path]).hexdigest(), 'sha256': digest(path),
            'selected': ['Jsp404.'+path.stem+'.cuts_checked']})
    (args.out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps({'status': manifest['status'], 'new_pieces': len(pieces), 'wrappers': len(wrappers),
                     'cuts': 235, 'max_work': max(x['work'] for x in mapping), 'first_work': mapping[0]['work']}), flush=True)


if __name__ == '__main__': main()
