#!/usr/bin/env python3
"""Generate new owned outer-left data/check targets without running Lean."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / '.lake/oct7-outer01/complete_known_catalog_result.json'
MANIFEST = ROOT / 'research/JSP404_N4_R2_OUTER_LEFT_SOURCE_MANIFEST_20261007.json'
CHECKPOINT = ROOT / 'research/JSP404_N4_R2_OUTER_LEFT_CHECKPOINT_20261007.json'
spec = importlib.util.spec_from_file_location('frozen_literal_format', ROOT / 'tools/export_n4_r2_named_leaf_replay_20261007.py')
fmt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fmt)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--block', action='append', type=int)
    args = parser.parse_args()
    selected = set(args.block) if args.block is not None else set(range(193))
    assert selected <= set(range(193))
    source = json.loads(INPUT.read_text())
    assert source['status'] == 'COMPLETE_DIAGNOSTIC_NOT_KERNEL' and source['words_checked'] == 24698
    records, registry = source['records'], source['cycles']
    assert [r['word_id'] for r in records] == list(range(24698))
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {'source_hashes': {}, 'blocks': {}}
    frozen = json.loads(CHECKPOINT.read_text()).get('passed_source_hashes', {}) if CHECKPOINT.exists() else {}
    manifest = dict(previous)
    manifest.update({'status': 'SOURCE_ONLY_NOT_KERNEL', 'Lean_compiled': False,
                     'input': str(INPUT.relative_to(ROOT)), 'input_sha256': sha(INPUT),
                     'generator': str(Path(__file__).resolve().relative_to(ROOT)), 'generator_sha256': sha(Path(__file__)),
                     'complete_words': 24698, 'leaf_chunk': 128,
                     'pure_module': 'Jsp000404.N4R2OuterLeftReplay',
                     'role_assignment': {'low': 1, 'unconstrained': 0, 'tails': [2, 3, 4, 5, 6]}})
    hashes = dict(previous.get('source_hashes', {}))
    blocks = dict(previous.get('blocks', {}))
    common = ('set_option autoImplicit false\nset_option pp.fullNames true\n'
              'set_option maxRecDepth 8192\nset_option maxHeartbeats 0\n'
              'set_option Elab.async false\n\n')

    def dispatch(lo, hi):
        if hi - lo == 1:
            return f'namedLeaf{lo:03d}'
        mid = (lo + hi) // 2
        return f'if offset < {mid} then ({dispatch(lo, mid)}) else ({dispatch(mid, hi)})'

    def proof(lo, hi, indent):
        prefix = ' ' * indent
        if hi - lo == 1:
            return (prefix + f'have hj : j = ⟨{lo}, by decide⟩ := by\n' +
                    prefix + '  apply Fin.ext\n' + prefix + f'  change j.val = {lo}\n' +
                    prefix + '  omega\n' + prefix + 'subst j\n' +
                    prefix + f'exact namedLeaf{lo:03d}_checked\n')
        mid = (lo + hi) // 2
        return (prefix + f'by_cases h{mid} : j.val < {mid}\n' +
                prefix + '· ' + proof(lo, mid, indent + 2).lstrip() +
                prefix + '· ' + proof(mid, hi, indent + 2).lstrip())

    for block in sorted(selected):
        start, count = 128 * block, min(128, 24698 - 128 * block)
        module = f'Jsp000404.N4R2OuterLeftLeafCheckedShard{block:03d}'
        namespace = f'Jsp404.N4R2OuterLeftData.LeafShard{block:03d}'
        chunk = records[start:start + count]
        cids = sorted({cid for r in chunk for cid in ([r['cycle']] if r['stage'] == 'TAIL' else r['cycles'])})
        local = {cid: i for i, cid in enumerate(cids)}
        lines = ['import Jsp000404.N4R2OuterLeftReplay\nimport Jsp000404.N4R2WordCatalog\n\n',
                 common, f'namespace {namespace}\nopen N4R2OuterLeftReplay\n\n']
        for cid in cids:
            c = registry[cid]
            n = len(c['c'])
            assert c['accepts'] and c['nodes'][0] == c['nodes'][-1]
            lines.extend([f'-- Cycle fingerprint {cid}.\n',
                          f'def localCycle{local[cid]:05d} : Cycle where\n  length := {n}\n  data := {{\n',
                          f'    node := {fmt.vector(fmt.VERTICES[v] for v in c["nodes"])}\n',
                          f'    constant := {fmt.vector(c["c"])}\n',
                          f'    coefficient := {fmt.vector(c["b"])}\n',
                          f'    strict := {fmt.vector(str(v).lower() for v in c["strict"])} }}\n',
                          f'  origin := {fmt.vector(fmt.origin(p) for p in c["premises"])}\n\n'])

        def library(lo, hi):
            if hi - lo == 1:
                return f'if id = {lo} then some localCycle{lo:05d} else none'
            mid = (lo + hi) // 2
            return f'if id < {mid} then ({library(lo, mid)}) else ({library(mid, hi)})'

        lines.append(f'def library : Library := fun id => {library(0, len(cids))}\n\n')
        for offset, record in enumerate(chunk):
            ranks = {i: {j: 0 for j in range(7) if j != i} for i in range(7)}
            for bit, (a, b, c) in zip(record['word'], fmt.TRIPLES):
                for row, u, v in ((a, b, c), (b, a, c), (c, a, b)):
                    ranks[row][v if bit == '0' else u] += 1
            assert all(sorted(ranks[i].values()) == list(range(6)) for i in range(7))
            rows = fmt.vector(fmt.vector(sorted(ranks[i], key=ranks[i].get)) for i in range(7))
            leaf = f'.tail {local[record["cycle"]]}' if record['stage'] == 'TAIL' else f'.low ({fmt.vector(local[cid] for cid in record["cycles"])})'
            lines.extend([f'def namedLeaf{offset:03d} : LeafData := {{ rows := {rows}, proof := {leaf} }}\n\n',
                          f'theorem namedLeaf{offset:03d}_checked :\n',
                          f'    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 {start + offset})) namedLeaf{offset:03d} = true :=\n',
                          '  by decide +kernel\n\n'])
        lines.extend(['def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }\n',
                      f'def lookup (offset : ℕ) : LeafData :=\n  if offset < {count} then ({dispatch(0, count)}) else fallback\n\n',
                      f'theorem point_checked (j : Fin {count}) :\n',
                      f'    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 ({start} + j.val))) (lookup j.val) = true := by\n',
                      f'  have hjbound : j.val < {count} := j.isLt\n', proof(0, count, 2), '\n',
                      f'theorem correct (id : Fin 24698) (hlow : {start} ≤ id.val) (hhigh : id.val < {start + count}) :\n',
                      f'    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - {start})) = true := by\n',
                      f'  let j : Fin {count} := ⟨id.val - {start}, by omega⟩\n',
                      f'  have hsum : {start} + j.val = id.val := by dsimp [j]; omega\n',
                      f'  have hindex : Fin.ofNat 24698 ({start} + j.val) = id := by\n',
                      '    apply Fin.ext\n    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]\n',
                      '  have hh := point_checked j\n  rw [hindex] at hh\n  exact hh\n\n',
                      '#print axioms point_checked\n#print axioms correct\n', f'end {namespace}\n'])
        relative = module.replace('.', '/') + '.lean'
        path, content = ROOT / relative, ''.join(lines)
        if path.exists() and path.read_text() != content:
            assert relative not in frozen, f'Refusing to alter PASS {relative}'
            assert sha(path) == previous['source_hashes'].get(relative), f'Foreign source collision {relative}'
        if not path.exists() or path.read_text() != content:
            path.write_text(content)
        hashes[relative] = sha(path)
        blocks[module] = {'start': start, 'count': count, 'cycles': cids,
                          'local_cycles': len(cids), 'source': relative, 'source_sha256': sha(path)}
    if len(blocks) == 193:
        modules = [f'Jsp000404.N4R2OuterLeftLeafCheckedShard{i:03d}' for i in range(193)]
        ranges = [(i, i * 128, min(128, 24698 - i * 128)) for i in range(193)]

        def all_dispatch(values, access):
            if len(values) == 1:
                return access(values[0])
            mid = len(values) // 2
            cut = values[mid][1]
            return f'if id.val < {cut} then ({all_dispatch(values[:mid], access)}) else ({all_dispatch(values[mid:], access)})'

        def all_proof(values, indent):
            prefix = ' ' * indent
            if len(values) == 1:
                return prefix + f'exact LeafShard{values[0][0]:03d}.correct id (by omega) (by omega)\n'
            mid = len(values) // 2
            cut = values[mid][1]
            return (prefix + f'by_cases h{cut} : id.val < {cut}\n' +
                    prefix + f'· simp only [leafData, libraryFor, h{cut}, ↓reduceIte]\n' +
                    all_proof(values[:mid], indent + 2) +
                    prefix + f'· simp only [leafData, libraryFor, h{cut}, ↓reduceIte]\n' +
                    all_proof(values[mid:], indent + 2))

        relative = 'Jsp000404/N4R2OuterLeftAllChecked.lean'
        content = (''.join(f'import {m}\n' for m in modules) + '\n' + common +
                   'namespace Jsp404.N4R2OuterLeftData\nopen N4R2OuterLeftReplay\n\n' +
                   'def libraryFor (id : Fin 24698) : Library :=\n  ' +
                   all_dispatch(ranges, lambda r: f'LeafShard{r[0]:03d}.library') + '\n\n' +
                   'def leafData (id : Fin 24698) : LeafData :=\n  ' +
                   all_dispatch(ranges, lambda r: f'LeafShard{r[0]:03d}.lookup (id.val - {r[1]})') + '\n\n' +
                   'theorem all_leaves_checked (id : Fin 24698) :\n'
                   '    leafCheck (libraryFor id) (N4R2WordTree.catalog id) (leafData id) = true := by\n' +
                   all_proof(ranges, 2) + '\n#print axioms all_leaves_checked\nend Jsp404.N4R2OuterLeftData\n')
        path = ROOT / relative
        if path.exists() and path.read_text() != content:
            assert relative not in frozen and sha(path) == previous['source_hashes'].get(relative)
        if not path.exists() or path.read_text() != content:
            path.write_text(content)
        hashes[relative] = sha(path)
        manifest['aggregate_module'] = 'Jsp000404.N4R2OuterLeftAllChecked'
    manifest['source_hashes'], manifest['blocks'] = hashes, blocks
    MANIFEST.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'status': manifest['status'], 'generated_blocks': len(selected),
                      'total_blocks': len(blocks), 'max_local_cycles': max(v['local_cycles'] for v in blocks.values()),
                      'aggregate_source': 'Jsp000404/N4R2OuterLeftAllChecked.lean' if len(blocks) == 193 else None}))


if __name__ == '__main__':
    main()
