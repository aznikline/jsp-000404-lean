#!/usr/bin/env python3
"""Check one owned outer-left target using the frozen genuine-check engine.

Only use in a formally allocated compute window. Evidence is stored in a
new ledger/log directory, never in the frozen between records.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def main():
    template = ROOT / 'tools/check_n4_r2_replay_module_v2_20261007.py'
    spec = importlib.util.spec_from_file_location('frozen_outer_check_engine', template)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    engine.CHECKPOINT = 'research/JSP404_N4_R2_OUTER_LEFT_CHECKPOINT_20261007.json'
    engine.LOGDIR = 'verification/n4-r2-outer-left-20261007'
    try:
        engine.main()
    finally:
        p = ROOT / engine.CHECKPOINT
        if p.exists():
            data = json.loads(p.read_text())
            data['outer_checker'] = str(Path(__file__).resolve().relative_to(ROOT))
            data['outer_checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
            data['scope'] = 'Only explicitly checked new outer-left modules; not all-word closure unless final aggregate and terminal are actually PASS.'
            p.write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
