#!/usr/bin/env python3
"""Check the scoped October 3 proof package; report the original root separately.

Run from the project after `lake build`:
    lake env python3 verification/oct3-review/verify_review.py
Default trust=0 rechecks imported proof objects. --trust=1 checks each new
source against the already compiled imports; use it only after source rebuilding.
The resulting PASS refers exclusively to the named scoped declarations.
A root containing sorryAx remains incomplete even when every scoped gate passes.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--trust', choices=['0', '1'], default='0')
args = parser.parse_args()
repo = Path(__file__).resolve().parents[2]
logs = repo / '.lake' / 'review-20261003'
logs.mkdir(parents=True, exist_ok=True)
lib = repo / '.lake' / 'build' / 'lib' / 'lean'
sources = [
    'Jsp000404/R2SixCentreN3.lean',
    'Jsp000404/N3Extraction.lean',
    'research/JSP404_R2_N3_CLOSURE_20261003.lean',
    'research/JSP404_JUMP_FAMILY_CLOSURE_20261003.lean',
    'research/JSP404_JUMP_STRIP_INDUCTION_20261003.lean',
    'research/JSP404_LOCAL_GEOMETRY_PRIMITIVES_20261003.lean',
    'verification/oct3-review/ReviewAudit.lean',
]
records = []
for source in sources:
    output = lib / Path(source).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    command = ['lean', f'--trust={args.trust}', '-o', str(output), source]
    result = subprocess.run(command, cwd=repo, capture_output=True, text=True)
    log = logs / (Path(source).stem + '.log')
    log.write_text(result.stdout + result.stderr)
    records.append({'source': source, 'source_sha256': hashlib.sha256((repo/source).read_bytes()).hexdigest(),
                    'command': command, 'exit_code': result.returncode, 'log': str(log.relative_to(repo))})
    print(f'{source}: exit {result.returncode}', flush=True)
    if result.returncode:
        print(result.stdout + result.stderr)
        (logs/'receipt.json').write_text(json.dumps({'trust':args.trust,'modules':records,'scoped_pass':False},indent=2)+'\n')
        raise SystemExit(result.returncode)

standard = {'propext', 'Classical.choice', 'Quot.sound'}
all_text = '\n'.join((logs/(Path(s).stem+'.log')).read_text() for s in sources)
matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", all_text)
axioms = {name:{a.strip() for a in values.split(',') if a.strip()} for name,values in matches}
required = ['Jsp404.six_centre_n3_terminal',
            'Jsp404.AirCandidate.n3_r2_centres_le_five',
            'Jsp404.AirCandidate.n3_r2_potential_le_ten',
            'Jsp404.sendov_of_jump_families',
            'Jsp404.JumpStripInduction20261003.sendov_of_actual_point_strip_bounds',
            'Jsp404.Oct3Local.positive_row_angle_outside',
            'Jsp404.Oct3Local.turn_budget_of_ray_windows']
fail = {name:sorted(axioms.get(name, {'MISSING'}) - standard) for name in required
        if name not in axioms or not axioms[name] <= standard}
root_complete = all(name in axioms and axioms[name] <= standard
                    for name in ['Jsp404.sendov_lower','Jsp404.sendov_upper'])
receipt = {'trust':args.trust,'modules':records,'scoped_pass':not fail,'unexpected_scoped_axioms':fail,
           'axioms':{name:sorted(values) for name,values in axioms.items()},
           'original_root_axiom_gate_pass':root_complete,
           'limitation':'Conditional strip/jump consumers remain conditional. A scoped pass does not prove the original root.'}
(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('SCOPED PASS' if not fail else 'SCOPED FAIL')
print('ORIGINAL ROOT AXIOM GATE: '+('PASS' if root_complete else 'REJECTED (still incomplete)'))
raise SystemExit(1 if fail else 0)
