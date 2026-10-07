#!/usr/bin/env python3
"""One new outer module with an isolated genuine evidence ledger."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def main():
    module = sys.argv[1]
    assert re.fullmatch(r'Jsp000404\.N4R2OuterLeft[A-Za-z0-9]+', module)
    relative = f'research/n4-r2-outer-left-module-checkpoints-20261007/{module.rsplit(".", 1)[1]}.json'
    path = ROOT / relative
    path.parent.mkdir(exist_ok=True)
    template = ROOT / 'tools/check_n4_r2_replay_module_v2_20261007.py'
    spec = importlib.util.spec_from_file_location('frozen_outer_isolated_engine', template)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    engine.CHECKPOINT = relative
    engine.LOGDIR = 'verification/n4-r2-outer-left-20261007'
    try:
        engine.main()
    finally:
        if path.exists():
            data = json.loads(path.read_text())
            data['isolated_outer_wrapper'] = str(Path(__file__).resolve().relative_to(ROOT))
            data['isolated_outer_wrapper_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
            path.write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
