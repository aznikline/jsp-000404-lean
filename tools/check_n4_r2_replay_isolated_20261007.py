#!/usr/bin/env python3
"""Run the frozen one-module checker with an isolated per-module ledger.

This avoids concurrent writers losing records in the aggregate checkpoint.
The checker template, wrapper, source, logs and artifacts retain exact hashes.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    assert len(sys.argv) >= 2
    module = sys.argv[1]
    assert re.fullmatch(r'Jsp000404\.N4R2[A-Za-z0-9]+', module)
    relative = f'research/n4-r2-replay-module-checkpoints-20261007/{module.rsplit(".", 1)[1]}.json'
    path = ROOT / relative
    path.parent.mkdir(exist_ok=True)
    template = ROOT / 'tools/check_n4_r2_replay_module_v2_20261007.py'
    spec = importlib.util.spec_from_file_location('n4_replay_checker_template', template)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    engine.CHECKPOINT = relative
    try:
        engine.main()
    finally:
        if path.is_file():
            ledger = json.loads(path.read_text())
            ledger['isolated_wrapper'] = str(Path(__file__).resolve().relative_to(ROOT))
            ledger['isolated_wrapper_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
            ledger['checker_template'] = str(template.relative_to(ROOT))
            ledger['checker_template_sha256'] = hashlib.sha256(template.read_bytes()).hexdigest()
            path.write_text(json.dumps(ledger, indent=2) + '\n')


if __name__ == '__main__':
    main()
