#!/usr/bin/env python3
"""Transport seven existing typed certificates to the common critical profile.

All direction hypotheses are copied from the existing Lean declarations and
checked against the ten-bit convention before any new source is written.
This exporter itself does not prove the resulting Lean declarations.
"""
from pathlib import Path
from itertools import combinations
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
MASKS = (1, 63, 74, 448, 512, 513, 948)
TRIPLES = tuple(combinations(range(5), 3))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    legacy = ROOT / 'Jsp000404/FourRowCertificate.lean'
    text = legacy.read_text()
    declarations = []
    provenance = []
    for mask in MASKS:
        match = re.search(
            rf'theorem orientation_{mask}_impossible \{{n : ℕ\}} '
            r'\(M : ModelSix n\)\n(.*?) : False := by', text, re.S)
        assert match, mask
        header = match.group(1)
        facts = re.findall(r'^    \(h(\d{3}) : (.*)\)$', header, re.M)
        assert len(facts) == 10, (mask, facts)
        row = re.search(
            r'\(hdef : SixModelCompression.rowDefect M ([13]) = 3\)', header)
        assert row, mask
        for bit, ((i, j, k), (label, actual)) in enumerate(zip(TRIPLES, facts)):
            assert label == f'{i}{j}{k}'
            x, y, z = f'M.d {i} {j}', f'M.d {i} {k}', f'M.d {j} {k}'
            expected = (f'{z} + 1 ≤ {x} ∧ {z} < {y} ∧ {y} < {x}'
                        if (mask >> bit) & 1 else
                        f'{x} + 1 ≤ {z} ∧ {x} < {y} ∧ {y} < {z}')
            assert actual == expected, (mask, bit, actual, expected)
        name = f'symbolic_mask{mask}_legacy_reuse'
        lines = [
            f'/-- The existing direction {mask} certificate in the common profile. -/',
            f'theorem {name} {{n : ℕ}} (M : SixModelCompression.ModelSix n)',
            '    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)',
            '    (hdef0 : SixModelCompression.rowDefect M 0 = 2)',
            '    (hdef1 : SixModelCompression.rowDefect M 1 = 3)',
            '    (hdef3 : SixModelCompression.rowDefect M 3 = 3)',
            '    (hdef4 : SixModelCompression.rowDefect M 4 = 2)',
        ]
        lines += [f'    (htri{label} : {statement})' for label, statement in facts]
        lines += [
            '    : False := by',
            f'  exact FourRowCertificate.orientation_{mask}_impossible M',
            '    ' + ' '.join(f'htri{label}' for label, _ in facts),
            f'    hdef{row.group(1)}',
            '',
            f'#print axioms {name}',
        ]
        declarations.append('\n'.join(lines))
        provenance.append({
            'mask': mask,
            'legacy_theorem': f'Jsp404.FourRowCertificate.orientation_{mask}_impossible',
            'new_theorem': f'Jsp404.SixExactFloorKernel.{name}',
            'defect_three_row': int(row.group(1)),
            'legacy_source_line': text[:match.start()].count('\n') + 1,
            'triangle_hypotheses': dict(facts),
        })
    source = ROOT / 'Jsp000404/SixSymbolicLegacyReuse.lean'
    source.write_text(
        'import Jsp000404.FourRowCertificate\n\n'
        '/-! Typed reuse of seven existing forall-strip certificates.\n'
        'The common profile is explicit; no direction-membership oracle is assumed. -/\n'
        'set_option pp.fullNames true\n\n'
        'namespace Jsp404.SixExactFloorKernel\n\n'
        + '\n\n'.join(declarations)
        + '\n\nend Jsp404.SixExactFloorKernel\n')
    manifest = {
        'status': 'SOURCE_ONLY_NOT_PROVED',
        'module': 'Jsp000404.SixSymbolicLegacyReuse',
        'source': str(source.relative_to(ROOT)),
        'source_sha256': sha(source),
        'generator': str(Path(__file__).resolve().relative_to(ROOT)),
        'generator_sha256': sha(Path(__file__).resolve()),
        'legacy_source': str(legacy.relative_to(ROOT)),
        'legacy_source_sha256': sha(legacy),
        'scope': 'ModelSix n, n>=4, delta>=1/2, defects (2,3,*,3,2), fixed direction',
        'exact_masks': list(MASKS),
        'triangle_bit_order': [list(t) for t in TRIPLES],
        'bit_zero': 'ascending',
        'bit_one': 'descending',
        'declarations': provenance,
    }
    path = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_SOURCE_MANIFEST_20261006.json'
    path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'source': manifest['source'], 'source_sha256': manifest['source_sha256'],
                      'lines': len(source.read_text().splitlines()), 'masks': list(MASKS)}))


if __name__ == '__main__':
    main()
