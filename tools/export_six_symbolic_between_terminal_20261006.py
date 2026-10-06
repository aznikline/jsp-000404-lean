#!/usr/bin/env python3
"""Generate complete ten-triangle coverage from actually checked common leaves.

This tool does not search for contradictions.  It audits and replays the saved
coverage tree; Lean must subsequently check every arithmetic cycle and leaf call.
It refuses to generate a public source while any of the 62 typed leaves is absent.
"""
from pathlib import Path
from itertools import combinations
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
TRIPLES = tuple(combinations(range(5), 3))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_registry():
    registry = {}

    def add(mask, module, theorem, freeze, source_hashes):
        source = module.replace('.', '/') + '.lean'
        assert sha(ROOT / source) == source_hashes[source]
        text = (ROOT / source).read_text()
        short = theorem.rsplit('.', 1)[1]
        assert re.search(rf'theorem {short}\b', text)
        assert mask not in registry
        registry[mask] = {'module': module, 'theorem': theorem,
                          'source': source, 'source_sha256': sha(ROOT / source),
                          'freeze': str(freeze.relative_to(ROOT)), 'freeze_sha256': sha(freeze)}

    zero = ROOT / 'research/JSP404_SIX_SYMBOLIC_MASK0_FREEZE_20261006.json'
    f = json.loads(zero.read_text())
    assert f['kernel'] == 'PASS' and f['normal_lake'] == 'PASS'
    add(0, 'Jsp000404.SixExactFloorKernelSymbolicMask000Probe',
        'Jsp404.SixExactFloorKernel.symbolic_mask0_probe', zero, f['source_hashes'])
    legacy = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_FREEZE_20261006.json'
    f = json.loads(legacy.read_text())
    assert f['status'] == 'READY_STRICT_AND_GENUINE_NORMAL_PASS'
    for declaration in f['declarations']:
        add(declaration['mask'], f['module'], declaration['new_theorem'], legacy,
            {f['source']: f['source_sha256']})
    for freeze in sorted((ROOT / 'research').glob('JSP404_SIX_SYMBOLIC_MASK*_SOURCE_FREEZE_20261006.json')):
        f = json.loads(freeze.read_text())
        if f.get('kernel') != 'PASS' or f.get('normal_lake') != 'PASS':
            continue
        mask, mirror = f['mask'], f['reflection_mask']
        source_hashes = f.get('source_hashes', f.get('sources_frozen_for_first_checks'))
        assert isinstance(source_hashes, dict)
        add(mask, f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Probe',
            f'Jsp404.SixExactFloorKernel.symbolic_mask{mask}_probe', freeze, source_hashes)
        if mirror != mask:
            add(mirror, f'Jsp000404.SixExactFloorKernelSymbolicMask{mask:03d}Reflection',
                f'Jsp404.SixExactFloorKernel.symbolic_mask{mirror}_probe', freeze, source_hashes)
    for freeze in sorted((ROOT / 'research').glob('JSP404_SIX_SYMBOLIC_V2_MASK*_SOURCE_FREEZE_20261006.json')):
        f = json.loads(freeze.read_text())
        if f.get('kernel') != 'PASS' or f.get('normal_lake') != 'PASS':
            continue
        mask, mirror = f['mask'], f['reflection_mask']
        add(mask, f['public_imports'][0], f['public_theorems'][0], freeze, f['source_hashes'])
        if mirror != mask:
            add(mirror, f['public_imports'][1], f['public_theorems'][1], freeze, f['source_hashes'])
    return registry


def audit_tree(tree):
    stats = {'splits': 0, 'cycle_leaves': 0, 'orientation_leaves': 0}
    masks, arms = set(), set()

    def visit(node, bit, mask, facts):
        if 'core' in node:
            assert set(node['core']) <= set(facts)
            edges = [facts[name] for name in node['core']]
            adjacency = {}
            for lo, hi in edges:
                adjacency.setdefault(lo, []).append(hi)

            def cyclic(vertex, path):
                if vertex in path:
                    return True
                return any(cyclic(next_vertex, path | {vertex})
                           for next_vertex in adjacency.get(vertex, ()))

            # Each edge is strictly increasing or has a positive unit gap.
            assert any(cyclic(v, set()) for v in adjacency)
            covered = {mask | (suffix << bit) for suffix in range(2 ** (10 - bit))}
            assert not arms & covered
            arms.update(covered)
            assert node['covered_full_arms'] == len(covered)
            stats['cycle_leaves'] += 1
            return
        if 'mask' in node:
            assert bit == 10 and node['mask'] == mask and mask not in masks and mask not in arms
            masks.add(mask)
            arms.add(mask)
            stats['orientation_leaves'] += 1
            return
        assert tuple(node['triple']) == TRIPLES[bit] and len(node['children']) == 2
        i, j, k = node['triple']
        x, y, z = (i, j), (i, k), (j, k)
        stats['splits'] += 1
        for arm, child in enumerate(node['children']):
            lo, hi = (x, z) if arm == 0 else (z, x)
            local = dict(zip((f'htr{i}{j}{k}{s}' for s in 'abc'),
                             ((lo, hi), (lo, y), (y, hi))))
            visit(child, bit + 1, mask | (arm << bit), {**facts, **local})

    visit(tree, 0, 0, {})
    assert stats == {'splits': 197, 'cycle_leaves': 136, 'orientation_leaves': 62}
    assert arms == set(range(1024))
    return stats, masks


def main():
    coverage = ROOT / 'research/six-score-n5-between-20261005/SixExactFloorKernelN5BetweenTerminal.json'
    data = json.loads(coverage.read_text())
    stats, masks = audit_tree(data['tree'])
    registry = checked_registry()
    missing = sorted(masks - set(registry))
    if missing:
        print(json.dumps({'status': 'NOT_READY_NO_SOURCE_WRITTEN',
                          'checked_common_directions': len(registry),
                          'missing_directions': missing, 'coverage': stats}))
        return
    assert set(registry) == masks
    name = 'symbolic_between_impossible'
    lines = [f'import {module}' for module in sorted({e['module'] for e in registry.values()})]
    lines += ['', '/-! Complete original ten-triangle disjunction coverage for all n>=4. -/',
              'set_option pp.fullNames true', 'namespace Jsp404.SixExactFloorKernel', '',
              'set_option maxHeartbeats 16000000 in',
              f'theorem {name} {{n : ℕ}} (M : SixModelCompression.ModelSix n)',
              '    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)']
    lines += [f'    (hdef{i} : SixModelCompression.rowDefect M {i} = {c})'
              for i, c in ((0, 2), (1, 3), (3, 3), (4, 2))]
    lines += ['    : False := by']

    def render(node, indent=2):
        pre = ' ' * indent
        if 'core' in node:
            return [pre + 'linarith only [' + ', '.join(node['core']) + ']']
        if 'mask' in node:
            args = ['M', 'hn4', 'hhigh', 'hdef0', 'hdef1', 'hdef3', 'hdef4']
            args += [f'htri{i}{j}{k}' for i, j, k in TRIPLES]
            return [pre + 'exact ' + registry[node['mask']]['theorem'] + ' ' + ' '.join(args)]
        i, j, k = node['triple']
        name = f'htri{i}{j}{k}'
        result = [pre + f'rcases M.triangle {i} {j} {k} (by decide) (by decide) with {name} | {name}']
        for child in node['children']:
            result += [pre + '·', pre + f'  have htr{i}{j}{k}a := {name}.1',
                       pre + f'  have htr{i}{j}{k}b := {name}.2.1',
                       pre + f'  have htr{i}{j}{k}c := {name}.2.2']
            result += render(child, indent + 2)
        return result

    lines += render(data['tree'])
    lines += ['', f'#print axioms {name}', 'end Jsp404.SixExactFloorKernel']
    source = ROOT / 'Jsp000404/SixExactFloorKernelSymbolicBetweenTerminal.lean'
    assert not source.exists(), 'Do not rewrite an existing terminal source.'
    source.write_text('\n'.join(lines) + '\n')
    manifest = {'status': 'SOURCE_ONLY_NOT_PROVED', 'source': str(source.relative_to(ROOT)),
                'source_sha256': sha(source), 'generator': str(Path(__file__).resolve().relative_to(ROOT)),
                'generator_sha256': sha(Path(__file__).resolve()),
                'coverage_tree': str(coverage.relative_to(ROOT)), 'coverage_tree_sha256': sha(coverage),
                'coverage': {**stats, 'all_1024_arms': True},
                'typed_leaf_registry': registry,
                'public_theorem': 'Jsp404.SixExactFloorKernel.' + name,
                'scope': 'ModelSix n, n>=4, HIGH, defects(2,3,*,3,2); no caller orientation hypothesis'}
    path = ROOT / 'research/JSP404_SIX_SYMBOLIC_BETWEEN_TERMINAL_SOURCE_MANIFEST_20261006.json'
    path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'status': manifest['status'], 'source_sha256': manifest['source_sha256'],
                      'lines': len(lines), 'bytes': source.stat().st_size, 'coverage': manifest['coverage']}))


if __name__ == '__main__':
    main()
