#!/usr/bin/env python3
"""Independent source and finite decoder parity, never a kernel proof."""
from pathlib import Path
import hashlib
import itertools
import json
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'research/JSP404_N4_R2_OUTER_LEFT_SOURCE_MANIFEST_20261007.json'
INPUT = ROOT / '.lake/oct7-outer01/complete_known_catalog_result.json'
OUT = ROOT / 'research/JSP404_N4_R2_OUTER_LEFT_SOURCE_PARITY_20261007.json'
TRIPLES = list(itertools.combinations(range(7), 3))
EDGES = list(itertools.combinations(range(7), 2))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vector(items):
    return '![' + ', '.join(map(str, items)) + ']'


def distance(i, j):
    return 8 + EDGES.index(tuple(sorted((i, j))))


def lower(p, k):
    if p is None:
        return 0
    return (3 if p == k else 0) if p < 7 else (2 if k in EDGES[p - 7] else 0)


def decode(word, ords, p, name):
    if match := re.fullmatch(r'ht([0-6])([ab])', name):
        i, side = int(match[1]), match[2]
        return (1 + i, 0, 0, 0, False) if side == 'a' else (0, 1 + i, 0, 1, False)
    if match := re.fullmatch(r'ht([0-5])([1-6])', name):
        i, j = int(match[1]), int(match[2]); assert j == i + 1
        return (1 + j, 1 + i, 0, 0, True)
    if match := re.fullmatch(r'hc([0-6])([0-6])([ab])', name):
        i, j = int(match[1]), int(match[2]); assert i < j
        return (distance(i, j), 1 + i, -1, 0, False) if match[3] == 'a' else (1 + j, distance(i, j), 3, 1, False)
    if match := re.fullmatch(r'htr([0-6])([0-6])([0-6])([abc])', name):
        i, j, k = map(int, match.groups()[:3]); assert i < j < k
        x, y, z = distance(i, j), distance(i, k), distance(j, k)
        lo, hi = (x, z) if word[TRIPLES.index((i, j, k))] == '0' else (z, x)
        return {'a': (hi, lo, -1, 0, False), 'b': (y, lo, 0, 0, True), 'c': (hi, y, 0, 0, True)}[match[4]]
    match = re.fullmatch(r'hgap([0-6])([0-6])(lower|upper)', name)
    assert match, name
    i, k, side = int(match[1]), int(match[2]), match[3]
    before = 1 + i if k == 0 else distance(i, ords[i][k - 1])
    after = 1 + i if k == 6 else distance(i, ords[i][k])
    c, b = (4, 1) if k == 6 else (0, 0)
    if side == 'lower':
        bound = lower(p, k) if i == 1 else 0
        return (after, before, c - bound, b, False)
    assert i >= 2, f'Invalid outer upper origin {name}'
    return (before, after, 2 - c, -b, True)


def main():
    manifest, raw = json.loads(MANIFEST.read_text()), json.loads(INPUT.read_text())
    assert manifest['input_sha256'] == sha(INPUT)
    assert len(manifest['blocks']) == 193 and len(raw['records']) == 24698
    ids, contexts, arc_count = [], 0, 0
    for module, block in sorted(manifest['blocks'].items()):
        path = ROOT / block['source']
        assert sha(path) == block['source_sha256'] == manifest['source_hashes'][block['source']]
        text = path.read_text()
        local = {cid: i for i, cid in enumerate(block['cycles'])}
        start, count = block['start'], block['count']
        assert start == 128 * int(module[-3:]) and count == min(128, 24698 - start)
        assert text.count('theorem namedLeaf') == count
        assert 'set_option Elab.async false' in text and 'Array LeafData' not in text
        for offset, record in enumerate(raw['records'][start:start + count]):
            assert record['word_id'] == start + offset
            word = record['word']
            ranks = {i: {j: set() for j in range(7) if j != i} for i in range(7)}
            for bit, (a, b, c) in zip(word, TRIPLES):
                for row, u, v in ((a, b, c), (b, a, c), (c, a, b)):
                    first, second = (u, v) if bit == '0' else (v, u)
                    ranks[row][second].add(first)
            ords = {i: sorted(ranks[i], key=lambda j: len(ranks[i][j])) for i in range(7)}
            for i, ordered in ords.items():
                assert sorted(len(v) for v in ranks[i].values()) == list(range(6))
                assert all(u in ranks[i][v] for k, u in enumerate(ordered) for v in ordered[k + 1:])
            rows = vector(vector(ords[i]) for i in range(7))
            if record['stage'] == 'TAIL':
                selected = [(None, record['cycle'])]
                proof = f'.tail {local[record["cycle"]]}'
            else:
                assert record['stage'] == 'LOW1' and len(record['cycles']) == 28
                selected = list(enumerate(record['cycles']))
                proof = f'.low ({vector(local[c] for c in record["cycles"])})'
            expected = f'def namedLeaf{offset:03d} : LeafData := {{ rows := {rows}, proof := {proof} }}'
            assert expected in text
            for p, cid in selected:
                contexts += 1
                c = raw['cycles'][cid]
                assert c['nodes'][0] == c['nodes'][-1]
                C, B, strict = sum(c['c']), sum(c['b']), any(c['strict'])
                assert B >= 0 and C + B <= 0 and (C + B < 0 or B > 0 or strict)
                for j, premise in enumerate(c['premises']):
                    arc_count += 1
                    expected_arc = decode(word, ords, p, premise)
                    actual = (c['nodes'][j], c['nodes'][j + 1], c['c'][j], c['b'][j], c['strict'][j])
                    assert expected_arc == actual, (record['word_id'], p, premise, expected_arc, actual)
            ids.append(record['word_id'])
    assert ids == list(range(24698))
    result = {'status': 'STATIC_SOURCE_AND_DECODER_PARITY_PASS_NOT_KERNEL',
              'Lean_compiled': False, 'kernel_all_words': False,
              'words': len(ids), 'blocks': len(manifest['blocks']), 'contexts': contexts,
              'arc_occurrences': arc_count, 'unique_cycles': len(raw['cycles']),
              'manifest_sha256': sha(MANIFEST), 'input_sha256': sha(INPUT),
              'tool_sha256': sha(Path(__file__)),
              'not_claimed': ['All193 genuine targets PASS', 'Scalar terminal ready', 'Actual outer closure', 'Original all-n theorem']}
    OUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
