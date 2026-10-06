#!/usr/bin/env python3
"""Use the frozen real single-process checker for distinct V2 artifact paths."""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    if '--mask' in sys.argv:
        mask = int(sys.argv[sys.argv.index('--mask') + 1])
    else:
        raise ValueError('An explicit V2 mask is required')
    freeze = json.loads((ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_MASK{mask}_SOURCE_FREEZE_20261006.json').read_text())
    for source, digest in {**freeze['source_hashes'], **freeze['helper_source_hashes']}.items():
        assert hashlib.sha256((ROOT / source).read_bytes()).hexdigest() == digest
    original = ROOT / 'tools/check_six_symbolic_mask_kernel_20261006.py'
    assert hashlib.sha256(original.read_bytes()).hexdigest() == '7d889a77cfbc50a207aecaca1e29f448539a10a5e28d4469f9f0a31e674d0136'
    script = original.read_text()
    script = script.replace('SixExactFloorKernelSymbolicMask', 'SixExactFloorKernelSymbolicV2Mask')
    script = script.replace('JSP404_SIX_SYMBOLIC_M{mask}_', 'JSP404_SIX_SYMBOLIC_V2_M{mask}_')
    script = script.replace('six-symbolic-mask{mask}-', 'six-symbolic-v2-mask{mask}-')
    exec(compile(script, str(original), 'exec'), {'__file__': str(original), '__name__': '__main__'})


if __name__ == '__main__':
    main()
