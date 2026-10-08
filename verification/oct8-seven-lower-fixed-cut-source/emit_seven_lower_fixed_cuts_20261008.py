#!/usr/bin/env python3
"""SOURCE_ONLY deterministic fixed-context decomposition of frozen CLOSED data.

No generation/search, solver, Lean, or alteration of any prior data/proof.
Every path carries its exact setter order, node ID, and remaining fuel.
"""
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = '6944959d1716d5afa68bb6fbd4fd9470a44d3e2fcc7a191f0cce3a7f7978f9e3'
VECTOR = lambda xs: '!['+', '.join(xs)+']'
BOOL = lambda x: 'true' if x else 'false'
NODES = 'SevenLowerBranchLibraries.nodes'
CYCLES = 'SevenLowerBranchLibraries.cycles'
CONTEXTS = 'SevenLowerFixedCutContexts'


def context_expression(path):
    result = 'emptyContext'
    for step in path:
        if step[0] == 'triangle': result = f'setTriangle ({result}) {step[1]} {BOOL(step[2])}'
        elif step[0] == 'heavy': result = f'setHeavy ({result}) {step[1]}'
        else: result = f'setPositive ({result}) {step[1]} {step[2]}'
    return result


def next_context(context, node, index):
    t, h, p = context
    if node['tag'] == 'triangle':
        i = node['triangle']; assert t[i] is None
        return (t[:i]+(bool(index),)+t[i+1:], h, p), ('triangle', i, bool(index))
    if node['tag'] == 'heavy':
        assert h is None
        return (t, index, p), ('heavy', index)
    assert node['tag'] == 'positive'
    i = node['row_slot']; assert p[i] is None
    return (t, h, p[:i]+(index,)+p[i+1:]), ('positive', i, index)


def header(namespace, imports):
    return '\n'.join(['import '+name for name in imports]+['',
        '/-! SOURCE_ONLY fixed-context certificate proof candidate. -/',
        'set_option autoImplicit false', 'set_option Elab.async false',
        'set_option maxRecDepth 32768', 'set_option maxHeartbeats 0', '',
        'namespace Jsp404.'+namespace, 'open SevenLowerReplay', ''])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    args = parser.parse_args()
    raw = args.json.read_bytes(); assert hashlib.sha256(raw).hexdigest() == EXPECTED
    data = json.loads(raw); nodes = data['nodes']
    assert data['status'] == 'SOURCE_DATA_CLOSED_NOT_KERNEL_CHECKED'
    assert (data['root'], data['fuel']) == (10813, 26)
    sizes = []
    for i, node in enumerate(nodes):
        assert all(0 <= child < i for child in node.get('children', []))
        sizes.append(1+sum(sizes[child] for child in node.get('children', [])))
    states, cuts = [], []
    def visit(identifier, fuel, context, path, entered=False):
        assert fuel > 0
        node = nodes[identifier]
        state_id = len(states)
        state = {'state': state_id, 'node': identifier, 'fuel': fuel, 'context': context,
                 'path': path, 'subtree_occurrences': sizes[identifier], 'children': []}
        states.append(state)
        eligible = entered or node['tag'] == 'heavy'
        if eligible and sizes[identifier] <= 256:
            cuts.append(state_id); state['cut'] = True
        else:
            assert node['tag'] in ('triangle', 'heavy')
            state['cut'] = False
            for k, child in enumerate(node['children']):
                updated, step = next_context(context, node, k)
                state['children'].append(visit(child, fuel-1, updated, path+[step], eligible))
        return state_id
    root_state = visit(data['root'], data['fuel'], ((None,)*20, None, (None,)*4), [])
    assert len(cuts) == 248 and len(states)-len(cuts) == 133
    groups, current, work = [], [], 0
    for cut in cuts:
        if current and work+states[cut]['subtree_occurrences'] > 1024:
            groups.append(current); current, work = [], 0
        current.append(cut); work += states[cut]['subtree_occurrences']
    if current: groups.append(current)
    assert len(groups) == 14 and max(states[c]['subtree_occurrences'] for c in cuts) == 249
    cut_locations = {cut: (group, local) for group, values in enumerate(groups) for local, cut in enumerate(values)}
    outputs, modules = {}, []
    text = header(CONTEXTS, ['Jsp000404.SevenLowerBranchLibraries'])
    for state in states:
        text += f'def context{state["state"]:03d} : Context :=\n  {context_expression(state["path"])}\n\n'
    outputs[ROOT/'Jsp000404'/f'{CONTEXTS}.lean'] = text+'end Jsp404.'+CONTEXTS+'\n'
    for group, values in enumerate(groups):
        namespace = f'SevenLowerFixedCutGroup{group:02d}'; modules.append('Jsp000404.'+namespace)
        text = header(namespace, ['Jsp000404.'+CONTEXTS])
        count = len(values)
        text += f'def contexts : Fin {count} → Context := '+VECTOR([f'{CONTEXTS}.context{c:03d}' for c in values])+'\n'
        text += f'def fuels : Fin {count} → ℕ := '+VECTOR([str(states[c]['fuel']) for c in values])+'\n'
        text += f'def ids : Fin {count} → ℕ := '+VECTOR([str(states[c]['node']) for c in values])+'\n\n'
        text += f'theorem cuts_checked : ∀ j : Fin {count},\n    check {NODES} {CYCLES} (fuels j) (contexts j) (ids j) = true := by decide\n\n'
        text += '#print axioms cuts_checked\nend Jsp404.'+namespace+'\n'
        outputs[ROOT/'Jsp000404'/f'{namespace}.lean'] = text
    namespace = 'SevenLowerBranchComposedRootCheck'
    text = header(namespace, ['Jsp000404.SevenLowerCheckCompose']+modules+['Mathlib.Tactic.FinCases'])
    def proof_reference(state_id):
        if states[state_id]['cut']:
            group, local = cut_locations[state_id]
            return f'(SevenLowerFixedCutGroup{group:02d}.cuts_checked {local})'
        return f'prefix{state_id:03d}_checked'
    for state in reversed(states):
        if state['cut']: continue
        sid, identifier, fuel = state['state'], state['node'], state['fuel']
        node, children, ctx = nodes[identifier], state['children'], f'{CONTEXTS}.context{sid:03d}'
        text += f'private theorem prefix{sid:03d}_checked :\n    check {NODES} {CYCLES} {fuel} {ctx} {identifier} = true := by\n'
        if node['tag'] == 'triangle':
            lo, hi = node['children']
            text += f'  apply SevenLowerCheckCompose.check_triangle_of_children {NODES} {CYCLES} {fuel-1} {ctx} {identifier} {node["triangle"]} {lo} {hi}\n'
            text += '  · rfl\n  · decide\n'
            for child in children: text += '  · exact '+proof_reference(child)+'\n'
        else:
            assert node['tag'] == 'heavy'
            text += f'  apply SevenLowerCheckCompose.check_heavy_of_children {NODES} {CYCLES} {fuel-1} {ctx} {identifier} ({VECTOR(list(map(str, node["children"])))})\n'
            text += '  · rfl\n  · decide\n  · intro p\n    fin_cases p\n'
            for child in children: text += '    · exact '+proof_reference(child)+'\n'
        text += '\n'
    text += f'theorem point_checked : check {NODES} {CYCLES} 26 emptyContext 10813 = true := by\n  exact {proof_reference(root_state)}\n\n#print axioms point_checked\nend Jsp404.{namespace}\n'
    outputs[ROOT/'Jsp000404'/f'{namespace}.lean'] = text
    assert not args.manifest.exists() and not args.manifest.parent.exists()
    assert all(not path.exists() for path in outputs)
    args.manifest.parent.mkdir(parents=True)
    manifest = {'status': 'SOURCE_ONLY_NOT_KERNEL_CHECKED', 'json_sha256': EXPECTED,
                'emitter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'root': 10813, 'fuel': 26, 'root_state': root_state,
                'cuts': cuts, 'states': states, 'groups': groups, 'modules': [],
                'solver_runs': 0, 'Lean_runs': 0, 'search_runs': 0}
    for path, text in outputs.items():
        path.write_text(text)
        manifest['modules'].append({'module': 'Jsp000404.'+path.stem, 'source': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size,
            'selected': [] if path.stem == CONTEXTS else ['Jsp404.'+path.stem+'.'+('point_checked' if path.stem == namespace else 'cuts_checked')]})
    (args.manifest.parent/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    args.manifest.write_text(json.dumps(manifest, indent=2)+'\n')
    (args.manifest.parent/'module-allowlist.txt').write_text('\n'.join(x['module'] for x in manifest['modules'])+'\n')
    (args.manifest.parent/'selected-allowlist.txt').write_text('\n'.join(name for x in manifest['modules'] for name in x['selected'])+'\n')
    print(json.dumps({'status': manifest['status'], 'cuts': len(cuts), 'prefix': len(states)-len(cuts),
        'groups': len(groups), 'max_cut': max(states[c]['subtree_occurrences'] for c in cuts),
        'max_group': max(sum(states[c]['subtree_occurrences'] for c in g) for g in groups),
        'modules': len(outputs)}), flush=True)


if __name__ == '__main__': main()
