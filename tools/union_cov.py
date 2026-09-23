#!/usr/bin/env python3
# union coverage: saved fat-arc cert / template-A / template-B / saved polygon
import json, glob, os, sys, subprocess
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generic_model as gm
from overfull_cert import verify_cert, CertError
from replay_cert import rebuild_orig
from template_cert import orig_ids, synth_chain

def scan(dpath):
    rep = subprocess.run(['python','-X','utf8','tools/replay_cert.py', dpath],
                         capture_output=True, text=True, encoding='utf-8').stdout
    fat, poly = set(), set()
    for line in rep.splitlines():
        if 'leaf_' not in line: continue
        nm = os.path.basename(line.split(':')[0].strip())
        if 'FAT_ARC' in line: fat.add(nm)
        if 'POLYGON' in line: poly.add(nm)
    stats = dict(fat_only=0, chain_only=0, both=0, neither=0, total=0)
    neither = []
    for f in sorted(glob.glob(os.path.join(dpath,'leaf_*.json'))):
        leaf = json.load(open(f, encoding='utf-8'))
        tau = F(str(leaf['target_tau']))
        rebuild_orig(leaf); ids = orig_ids()
        met = False
        for i0 in range(leaf['s']):
            ln = len(leaf['skeleton'][i0]['order'])
            for p in range(ln):
                for L in range(2, ln):
                    for var in 'ABC':
                        r = synth_chain(leaf, ids, i0, p, L, var)
                        if r and r[1] >= r[0]*tau: met = True
        nm = os.path.basename(f); stats['total']+=1
        hf = nm in fat or nm in poly
        if hf and met: stats['both']+=1
        elif hf: stats['fat_only']+=1
        elif met: stats['chain_only']+=1
        else: stats['neither']+=1; neither.append(nm)
    print(dpath, stats)
    print('  neither sample:', neither[:10])

for d in sys.argv[1:]: scan(d)
