#!/usr/bin/env python3
"""Reuse the frozen single-slot compiler checker for the semantic leaf module."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    frozen = json.loads((ROOT / 'research/JSP404_N4_R2_SHARED_CYCLE_CHECKER_RECEIPT_20261006b.json').read_text())
    base = ROOT / 'tools/check_n4_r2_shared_cycle_checker_20261006b.py'
    assert hashlib.sha256(base.read_bytes()).hexdigest() == frozen['script_sha256']
    code = base.read_text()
    code = code.replace('N4R2SharedCycleChecker', 'N4R2SharedLeafChecker')
    code = code.replace('JSP404_N4_R2_SHARED_CYCLE_CHECKER_RECEIPT_20261006b',
                        'JSP404_N4_R2_SHARED_LEAF_CHECKER_RECEIPT_20261007')
    code = code.replace('n4-r2-shared-cycle-checker-20261006b', 'n4-r2-shared-leaf-checker-20261007')
    code = code.replace('Shared Boolean cycle checker and genuine actual-row bridges only; not kernel all24698/bare8.',
                        'Shared typed-origin leaf checker with actual complete low profiles; not concrete kernel all24698/bare8.')
    exec(compile(code, str(base), 'exec'), {'__file__': str(Path(__file__).resolve()), '__name__': '__main__'})


if __name__ == '__main__':
    main()
