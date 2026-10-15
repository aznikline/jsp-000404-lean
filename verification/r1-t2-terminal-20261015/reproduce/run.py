"""Fresh or resumable guarded macOS reproduction of the actual Fin7 terminal."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

V = Path(__file__).resolve().parent
W = V.parents[2]

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--check-config', action='store_true')
    args = p.parse_args()
    if sys.platform != 'darwin':
        raise SystemExit('This runner uses the original macOS resource guard.')
    if (W / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.0':
        raise SystemExit('Pinned Lean toolchain differs.')
    if hashlib.sha256((W / 'lake-manifest.json').read_bytes()).hexdigest() != '60282c6b881335792e80bb0a7df1be42e900a7be96cc36fd5ab49172ca0ccff3':
        raise SystemExit('Pinned dependency manifest differs.')
    pins = json.loads((V / 'root_source_pins.json').read_text())['modules']
    for module, expected in pins.items():
        path = W / (('ThirdParty/Sendov/' if module.startswith('JSP404.') else '') + module.replace('.', '/') + '.lean')
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit('Pinned source differs: ' + module)
    subprocess.run(['elan', 'which', 'lean'], cwd=W, check=True)
    if args.check_config:
        print(f'Configuration ready: {len(pins)} pinned project modules. No kernel verification was run.')
        return
    subprocess.run([sys.executable, str(V / 'run_local_t2.py')], cwd=W, check=True)
    state = json.loads((V / 'batch_state.json').read_text())
    if state.get('current') or state.get('stopped') or state['modules'].get('Jsp000404.R1DispatchT2', {}).get('state') != 'PASSED':
        raise SystemExit('Kernel batch incomplete; inspect retained state and raw logs before resuming.')
    subprocess.run([sys.executable, str(V / 'run_terminal_probe.py')], cwd=W, check=True)
    subprocess.run([sys.executable, str(V / 'check_local_t2.py')], cwd=W, check=True)

if __name__ == '__main__':
    main()
