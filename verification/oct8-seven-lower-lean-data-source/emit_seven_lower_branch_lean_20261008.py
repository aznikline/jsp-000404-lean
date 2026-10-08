#!/usr/bin/env python3
"""Deterministic conversion of one frozen CLOSED JSON into SOURCE_ONLY Lean.

No search, solver, Lean, native_decide, or unsafe trust step. Existing paths
are rejected before writing. Finite root closure is still a kernel obligation.
"""
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = '6944959d1716d5afa68bb6fbd4fd9470a44d3e2fcc7a191f0cce3a7f7978f9e3'
CYCLE_CHUNK, NODE_CHUNK, SHARDS = 1024, 1536, 8
VECTOR = lambda xs: '!['+', '.join(xs)+']'
BOOL = lambda value: 'true' if value else 'false'


def vertex(value):
    if value == ['z']: return '.zero'
    if value[0] == 't': return f'.theta {value[1]}'
    assert value[0] == 'd' and value[1] < value[2]
    return f'.distance {value[1]} {value[2]}'


def origin(value):
    if value[0] == 'gapLower':
        _, i, k, order = value
        assert sorted(order) == [j for j in range(6) if j != i] and 0 <= k < 6
        return f'.gapLower {i} {k} ({VECTOR(list(map(str, order)))})'
    assert value[0] in ('thetaLower', 'thetaUpper', 'thetaOrder', 'corridorLower', 'corridorUpper', 'triangle')
    return '.'+value[0]+' '+' '.join(map(str, value[1:]))


def cycle_definition(name, cycle):
    assert cycle and all(edge['target'] == cycle[(i+1) % len(cycle)]['source'] for i, edge in enumerate(cycle))
    a, b = sum(edge['constant'] for edge in cycle), sum(edge['coefficient'] for edge in cycle)
    assert all(edge['coefficient'] in (0, 1) for edge in cycle)
    assert b >= 0 and a+b <= 0 and (a+b < 0 or b > 0 or any(edge['strict'] for edge in cycle))
    nodes = [edge['source'] for edge in cycle]+[cycle[-1]['target']]
    return '\n'.join([f'def {name} : Cycle where', f'  length := {len(cycle)}', '  data := {',
        '    node := '+VECTOR([vertex(v) for v in nodes]),
        '    constant := '+VECTOR([f'({edge["constant"]})' for edge in cycle]),
        '    coefficient := '+VECTOR([str(edge['coefficient']) for edge in cycle]),
        '    strict := '+VECTOR([BOOL(edge['strict']) for edge in cycle])+' }',
        '  origin := '+VECTOR([origin(edge['origin']) for edge in cycle]), ''])


def node_value(node):
    if node['tag'] == 'leaf': return f'.leaf {node["cycle"]}'
    children = node['children']
    if node['tag'] == 'triangle':
        assert len(children) == 2
        return f'.triangle {node["triangle"]} {children[0]} {children[1]}'
    if node['tag'] == 'heavy':
        assert len(children) == 21
        return '.heavy ('+VECTOR(list(map(str, children)))+')'
    assert node['tag'] == 'positive' and len(children) == 6
    return f'.positive {node["row_slot"]} ('+VECTOR(list(map(str, children)))+')'


def header(namespace, imports):
    return '\n'.join(['import '+name for name in imports]+['',
        '/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/',
        'set_option autoImplicit false', 'set_option Elab.async false',
        'set_option maxRecDepth 8192', 'set_option maxHeartbeats 0', '',
        'namespace Jsp404.'+namespace, 'open SevenLowerReplay', ''])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    args = parser.parse_args()
    raw = args.json.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED
    data = json.loads(raw)
    assert data['status'] == 'SOURCE_DATA_CLOSED_NOT_KERNEL_CHECKED'
    assert (data['root'], data['fuel'], len(data['nodes']), len(data['cycles'])) == (10813, 26, 10814, 7104)
    depths = []
    for i, node in enumerate(data['nodes']):
        children = node.get('children', [])
        assert all(type(child) is int and 0 <= child < i for child in children)
        if node['tag'] == 'leaf': assert 0 <= node['cycle'] < len(data['cycles'])
        depths.append(1+max((depths[child] for child in children), default=0))
    assert depths[data['root']] == data['fuel']
    outputs, modules = {}, []
    for shard in range(SHARDS):
        namespace = f'SevenLowerBranchShard{shard:02d}'
        module = 'Jsp000404.'+namespace; modules.append(module)
        text = header(namespace, ['Jsp000404.SevenLowerReplay'])
        cycles = data['cycles'][shard*CYCLE_CHUNK:(shard+1)*CYCLE_CHUNK]
        for local, cycle in enumerate(cycles): text += cycle_definition(f'cycle{local:04d}', cycle)+'\n'
        text += 'def cycles : CycleLibrary\n'+''.join(f'  | {i} => some cycle{i:04d}\n' for i in range(len(cycles)))+'  | _ => none\n\n'
        nodes = data['nodes'][shard*NODE_CHUNK:(shard+1)*NODE_CHUNK]
        text += 'def nodes : NodeLibrary\n'+''.join(f'  | {i} => some ({node_value(node)})\n' for i, node in enumerate(nodes))+'  | _ => none\n\n'
        outputs[ROOT/'Jsp000404'/f'{namespace}.lean'] = text+'end Jsp404.'+namespace+'\n'
    namespace = 'SevenLowerBranchLibraries'
    text = header(namespace, modules)
    for field, chunk, library in [('cycles', CYCLE_CHUNK, 'CycleLibrary'), ('nodes', NODE_CHUNK, 'NodeLibrary')]:
        text += f'def {field} (id : ℕ) : Option '+('Cycle' if field == 'cycles' else 'Node')+f' :=\n  match id / {chunk} with\n'
        text += ''.join(f'  | {s} => SevenLowerBranchShard{s:02d}.{field} (id % {chunk})\n' for s in range(SHARDS))+'  | _ => none\n\n'
    outputs[ROOT/'Jsp000404'/f'{namespace}.lean'] = text+'end Jsp404.'+namespace+'\n'
    namespace = 'SevenLowerBranchPilot'
    text = header(namespace, ['Jsp000404.SevenLowerReplay'])+cycle_definition('firstCycle', data['cycles'][0])+'\n'
    tri, heavy, positive = data['first_closed_context']
    option = lambda x, boolean=False: 'none' if x is None else '(some '+(BOOL(x) if boolean else str(x))+')'
    text += 'def firstContext : Context :=\n  ⟨'+VECTOR([option(x, True) for x in tri])+', '+option(heavy)+', '+VECTOR([option(x) for x in positive])+'⟩\n\n'
    text += 'theorem first_cycle_checked : firstCycle.check firstContext = true := by decide\n\n#print axioms first_cycle_checked\n'
    outputs[ROOT/'Jsp000404'/f'{namespace}.lean'] = text+'end Jsp404.'+namespace+'\n'
    namespace = 'SevenLowerBranchRootCheck'
    text = header(namespace, ['Jsp000404.SevenLowerBranchLibraries'])
    text += 'theorem point_checked : check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles\n    26 emptyContext 10813 = true := by decide\n\n#print axioms point_checked\n'
    outputs[ROOT/'Jsp000404'/f'{namespace}.lean'] = text+'end Jsp404.'+namespace+'\n'
    assert not args.manifest.exists() and all(not path.exists() for path in outputs)
    args.manifest.parent.mkdir(parents=True, exist_ok=False)
    manifest = {'status': 'SOURCE_ONLY_NOT_KERNEL_CHECKED', 'json_sha256': EXPECTED,
                'emitter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'root': 10813, 'fuel': 26, 'cycle_chunk': CYCLE_CHUNK, 'node_chunk': NODE_CHUNK,
                'solver_runs': 0, 'Lean_runs': 0, 'modules': []}
    for path, text in outputs.items():
        path.write_text(text)
        manifest['modules'].append({'module': 'Jsp000404.'+path.stem, 'source': str(path.relative_to(ROOT)),
                                    'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size,
                                    'prints': 1 if path.stem.endswith(('Pilot', 'RootCheck')) else 0})
    (args.manifest.parent/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    args.manifest.write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps({'status': manifest['status'], 'modules': len(outputs), 'source_bytes': sum(x['bytes'] for x in manifest['modules'])}), flush=True)


if __name__ == '__main__': main()
