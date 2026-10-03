from pathlib import Path
from hashlib import sha256
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OWNER = Path('/Users/wizout/op/learn/sunyuchen/jsp-wt-air-owner')
LIFT = Path('/Users/wizout/op/learn/sunyuchen/jsp-wt-merge/research/JSP404_R2_N3_CLOSURE_20261003.lean')
EXPECTED = {
    'Jsp000404/R2SixCentreN3.lean': '7568c8d21192025bc42b29b6433da6a9ecc332a029649bcfeff42e6b846e09f2',
    'Jsp000404/N3Extraction.lean': '654ede99876d4eb530b7faec07b098acc4f00bb0a6f79d6619a1ac38977a2f76',
}
shutil.copytree(OWNER / '.lake/build/lib/lean/Jsp000404',
    ROOT / 'lib/Jsp000404', dirs_exist_ok=True)
for name, digest in EXPECTED.items():
    assert sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
(ROOT / 'research' / LIFT.name).write_bytes(LIFT.read_bytes())
env = os.environ.copy()
base_path = env.get('LEAN_PATH', '')
env['LEAN_PATH'] = str(ROOT / 'lib') + ':' + base_path
sources = [*EXPECTED, 'research/' + LIFT.name]
manifest = {
    'remote_pin': '8365f3cb5ec3738ecb8787c14a2514e6e7e4bb46',
    'candidate_provenance': 'Unpublished local scalar and repaired extraction, plus new scoped deletion lift; no remote delivery claim.',
    'owner_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=OWNER, text=True).strip(),
    'dependency_cache': str(OWNER / '.lake/build/lib/lean'),
    'base_lean_path': base_path,
    'source_sha256': {s: sha256((ROOT / s).read_bytes()).hexdigest() for s in sources},
    'core_source_sha256': {name: sha256((OWNER / 'Jsp000404' / (name + '.lean')).read_bytes()).hexdigest()
        for name in ['R2SixCentre', 'FivePointCapacity', 'MixedStarExclusion', 'GeometricDeletion', 'DeletionRigidity', 'Deletion']},
    'dependency_olean_sha256': {str(p.relative_to(ROOT / 'lib')): sha256(p.read_bytes()).hexdigest()
        for p in (ROOT / 'lib/Jsp000404').glob('*.olean')
        if p.stem not in ['R2SixCentreN3', 'N3Extraction']},
    'checks': [],
}
(ROOT / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
for name in sources:
    stem = Path(name).stem
    out = ROOT / 'lib' / Path(name).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    log = ROOT / 'logs' / (stem + '.log')
    command = ['lean', '--trust=0', '-R', str(ROOT), '-o', str(out), str(ROOT / name)]
    print('checking ' + name, flush=True)
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=OWNER, env=env, stdout=stream, stderr=subprocess.STDOUT)
    manifest['checks'].append({'source': name, 'command': command, 'log': str(log), 'exit_code': result.returncode})
    (ROOT / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('exit=' + str(result.returncode) + ' log=' + str(log), flush=True)
    if result.returncode:
        print(log.read_text(), flush=True)
        sys.exit(result.returncode)
print('candidate verification passed', flush=True)
