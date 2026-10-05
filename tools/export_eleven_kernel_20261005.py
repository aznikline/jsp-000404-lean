#!/usr/bin/env python3
"""Replay exact eleven-point DBM evidence and prune ordinary proof dependencies.

Frozen mathematical/search sources are only imported.  Every selected arm and
original atom index is retained in the raw evidence.  A forced split is removed
only when its surviving proof uses none of its introduced original atoms.
Binary splits always retain both arms.  No DBM verdict is a Lean premise.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import ctypes as C
import gzip
import hashlib
import json
from pathlib import Path
import pickle
import re
import subprocess
import tempfile
import time

import dbm_eleven_optimized_20261005 as opt

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "research/JSP404_ELEVEN_KERNEL_EXPORT_20261005.json"
EVIDENCE = ROOT / "research/JSP404_ELEVEN_KERNEL_TREE_20261005.pickle.gz"
NS = "Jsp404.NoSatElevenDBMTerminal"


class RecordingSearch(opt.Search):
    def wrap(self, chain, node):
        for idx, rejected, core in reversed(chain):
            node = (idx, rejected, core, node)
        return node

    def tree(self, dbm, pending, depth=0):
        self.stats["saturated_entries"] += 1
        chain = []
        while True:
            self.tick(depth + len(chain))
            pending, chosen, mask, removed = self.scan(dbm, pending)
            self.stats["redundant_triangles_removed"] += removed
            if not pending:
                raise opt.audited.FeasibleDBM(dbm)
            if chosen < 0:
                break
            self.stats["forced_splits"] += 1
            remaining = [t for t in pending if t != chosen]
            rejected = {}
            for q, arm in enumerate(self.arms[chosen]):
                if mask & (1 << q):
                    core = next(c for e in arm if (c := dbm.immediate_cycle(e)) is not None)
                    self.note_cycle(core)
                    rejected[q] = core
            if len(rejected) == 2:
                self.stats["terminal_states"] += 1
                return self.wrap(chain, (chosen, rejected[0], rejected[1]))
            dead = next(iter(rejected))
            survivor = 1 - dead
            self.stats["forced_survivor_additions"] += 1
            core = self.add_arm(dbm, self.arms[chosen][survivor])
            chain.append((chosen, dead, rejected[dead]))
            if core is not None:
                self.note_cycle(core)
                self.stats["terminal_states"] += 1
                return self.wrap(chain, core)
            pending = remaining
        chosen = self.rank_native(dbm, pending)
        self.stats["branch_splits"] += 1
        remaining = [t for t in pending if t != chosen]
        children = []
        for arm in self.arms[chosen]:
            self.check_budget()
            child = dbm.copy()
            self.stats["matrix_copies"] += 1
            core = self.add_arm(child, arm)
            if core is not None:
                self.note_cycle(core)
                children.append(core)
            else:
                children.append(self.tree(child, remaining, depth + len(chain) + 1))
        return self.wrap(chain, (chosen, *children))

    def replay(self):
        dbm = opt.NativeDBM(self.lib)
        for edge in self.base:
            core = dbm.add(edge)
            assert core is None
        return self.tree(dbm, list(range(len(self.triples))))


class Exporter:
    def __init__(self, search):
        self.search = search
        self.atoms, self.arms = search.atoms, search.arms
        self.base_mask = sum(1 << e[3] for e in search.base)
        self.arm_masks = [tuple(sum(1 << e[3] for e in arm) for arm in arms)
                          for arms in search.arms]
        self.metadata = {}
        self.removed_forced = 0

    def audit(self, node, scope):
        if isinstance(node, int):
            assert node and node & ~scope == 0, "cycle contains an out-of-scope original atom"
            return
        idx = node[0]
        if len(node) == 4:
            _, dead, core, child = node
            self.audit(core, scope | self.arm_masks[idx][dead])
            self.audit(child, scope | self.arm_masks[idx][1-dead])
        else:
            assert len(node) == 3
            for q, child in enumerate(node[1:]):
                self.audit(child, scope | self.arm_masks[idx][q])

    def prune(self, node, scope):
        if isinstance(node, int):
            assert node & ~scope == 0
            self.metadata[id(node)] = {"need": node, "checks": 1,
                                       "forced": 0, "binary": 0, "depth": 0}
            return node
        idx = node[0]
        if len(node) == 4:
            _, dead, core, child = node
            winner_mask = self.arm_masks[idx][1-dead]
            child = self.prune(child, scope | winner_mask)
            cm = self.metadata[id(child)]
            if not cm["need"] & winner_mask:
                self.removed_forced += 1
                assert cm["need"] & ~scope == 0
                return child
            assert core & ~(scope | self.arm_masks[idx][dead]) == 0
            need = (cm["need"] & ~winner_mask) | (core & ~self.arm_masks[idx][dead])
            pruned = (idx, dead, core, child)
            metadata = {"need": need, "checks": cm["checks"]+1,
                        "forced": cm["forced"]+1, "binary": cm["binary"],
                        "depth": cm["depth"]+1}
        else:
            children = [self.prune(child, scope | self.arm_masks[idx][q])
                        for q, child in enumerate(node[1:])]
            cms = [self.metadata[id(child)] for child in children]
            need = ((cms[0]["need"] & ~self.arm_masks[idx][0]) |
                    (cms[1]["need"] & ~self.arm_masks[idx][1]))
            pruned = (idx, *children)
            metadata = {"need": need, "checks": sum(cm["checks"] for cm in cms),
                        "forced": sum(cm["forced"] for cm in cms),
                        "binary": 1+sum(cm["binary"] for cm in cms),
                        "depth": 1+max(cm["depth"] for cm in cms)}
        assert need & ~scope == 0, "pruning leaked an unbound original atom"
        self.metadata[id(pruned)] = metadata
        return pruned

    def ids(self, bits):
        while bits:
            b = bits & -bits
            yield b.bit_length()-1
            bits ^= b

    def names(self, bits):
        return sorted({self.atoms[i]["name"] for i in self.ids(bits)})

    def pattern(self, idx):
        i,j,k = self.search.triples[idx]
        return "⟨"+", ".join(f"htr{i}{j}{k}{s}" for s in "abc")+", _, _⟩"

    def leaf_lines(self, core, indent):
        return [" "*indent+"linarith only [hlam, "+", ".join(self.names(core))+"]"]

    def render(self, node, indent=2, cuts=None):
        if cuts is not None and id(node) in cuts:
            number, incoming = cuts[id(node)]
            args = " ".join(self.atoms[a]["name"] for a in incoming)
            return [" "*indent+f"exact shard_{number:03d} m"+(" "+args if args else "")]
        if isinstance(node,int):
            return self.leaf_lines(node,indent)
        idx=node[0]
        i,j,k=self.search.triples[idx]
        prefix=" "*indent
        pattern=self.pattern(idx)
        if len(node)==4:
            _,dead,core,child=node
            method="resolve_left" if dead==0 else "resolve_right"
            lines=[prefix+f"have hforced{i}{j}{k} := (m.htr {i} {j} {k} (by decide) (by decide)).{method} (by",
                   prefix+"  rintro "+pattern]
            lines+=self.leaf_lines(core,indent+2)
            lines[-1]+=")"
            lines.append(prefix+f"obtain {pattern} := hforced{i}{j}{k}")
            return lines+self.render(child,indent,cuts)
        lines=[prefix+f"rcases m.htr {i} {j} {k} (by decide) (by decide) with",
               prefix+"  "+pattern+" | "+pattern]
        for child in node[1:]:
            lines.append(prefix+"·")
            lines+=self.render(child,indent+2,cuts)
        return lines

    def atom_type(self, idx):
        atom=self.atoms[idx]
        u,v,w=atom["from"],atom["to"],atom["packed_bound"]
        def val(vertex):
            if not vertex:return "(0 : ℝ)"
            i,j=self.search.chords[vertex-1]
            return f"m.d {i} {j}"
        if w==0 and v==0:return f"0 ≤ {val(u)}"
        if w==-4:return f"{val(v)} + lam ≤ {val(u)}"
        if w==-1:return f"{val(v)} < {val(u)}"
        if w==15 and u==0:return f"{val(v)} < 4*lam"
        if w==11:return f"{val(v)} - {val(u)} < 3*lam"
        raise ValueError(atom)

    def setup(self, need):
        names=set(self.names(need & self.base_mask))
        lines=["  have hlam := m.hlam", "  have hp := m.hp"]
        for i,j in self.search.chords:
            a,b=f"hd{i}{j}a",f"hd{i}{j}b"
            if not names & {a,b}:continue
            if b not in names:
                lines.append(f"  have {a} := (m.hrange {i} {j} (by decide)).1")
                continue
            lines += [f"  obtain ⟨{a}, {b}raw⟩ := m.hrange {i} {j} (by decide)",
                      f"  have {b} : m.d {i} {j} < 4*lam := by",
                      f"    linarith only [{b}raw, hp]"]
        for i,j,k in self.search.triples:
            if not names & {f"hc{i}{j}{k}{s}" for s in ("xy","yx","yz","zy")}:continue
            lines.append(f"  obtain ⟨hc{i}{j}{k}xy, hc{i}{j}{k}yx, hc{i}{j}{k}yz, hc{i}{j}{k}zy⟩ := endpoint_caps m {i} {j} {k} (by decide) (by decide)")
        return lines

    def model_source(self):
        return f'''import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Original necessary eleven-point angle model.  Every triangle retains
its separation, strict betweenness, and both endpoint caps. -/
namespace {NS}

structure ElevenModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : p < 4*lam
  d : Fin 11 → Fin 11 → ℝ
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin 11, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

theorem endpoint_caps {{lam p : ℝ}} (m : ElevenModel lam p)
    (i j k : Fin 11) (hij : i < j) (hjk : j < k) :
    m.d i k-m.d i j < 3*lam ∧
    m.d i j-m.d i k < 3*lam ∧
    m.d j k-m.d i k < 3*lam ∧
    m.d i k-m.d j k < 3*lam := by
  have hp := m.hp
  have hlam := m.hlam
  rcases m.htr i j k hij hjk with h | h
  all_goals rcases h with ⟨ha, hb, hc, hd, he⟩
  all_goals repeat' apply And.intro
  all_goals linarith

#print axioms endpoint_caps
end {NS}
'''

    def plan(self, tree, max_checks):
        shards=[]
        cuts={}
        def visit(node,scope):
            if isinstance(node,int):return
            if self.metadata[id(node)]["checks"]<=max_checks:
                need=self.metadata[id(node)]["need"]
                incoming=tuple(self.ids(need & scope & ~self.base_mask))
                number=len(shards)
                shards.append((node,incoming))
                cuts[id(node)]=(number,incoming)
                return
            idx=node[0]
            if len(node)==4:
                visit(node[3],scope|self.arm_masks[idx][1-node[1]])
            else:
                for q,child in enumerate(node[1:]):visit(child,scope|self.arm_masks[idx][q])
        visit(tree,self.base_mask)
        return shards,cuts

    def shard_source(self, number, node, incoming):
        name=f"shard_{number:03d}"
        prems=[f"    ({self.atoms[a]['name']} : {self.atom_type(a)})" for a in incoming]
        body=self.setup(self.metadata[id(node)]["need"])+self.render(node)
        lines=["set_option maxHeartbeats 32000000 in",
               f"private theorem proof_{name} {{lam p : ℝ}} (m : ElevenModel lam p)"]
        lines+=prems+["    : False := by"]+body
        lines += ["", f"theorem {name} {{lam p : ℝ}} (m : ElevenModel lam p)"]+prems
        lines += ["    : False :=", f"  proof_{name} m"+(" "+" ".join(self.atoms[a]['name'] for a in incoming) if incoming else "")]
        return ("import Jsp000404.NoSatElevenDBMModel\n\nnamespace "+NS+"\n\n"+
                "\n".join(lines)+f"\n\n#print axioms {name}\nend {NS}\n")

    def terminal_source(self, tree, shards, cuts):
        lines=[f"import Jsp000404.NoSatElevenDBMShard{i:03d}" for i in range(len(shards))]
        body=self.render(tree,cuts=cuts)
        # Include base facts referenced directly in root, excluding shard-local facts.
        names=set()
        for line in body:
            match=re.search(r"linarith only \[([^\]]*)\]",line)
            if match:names.update(s.strip() for s in match.group(1).split(','))
        need=sum(1<<i for i,a in enumerate(self.atoms) if a['name'] in names and (1<<i)&self.base_mask)
        lines += ["",f"namespace {NS}","", "set_option maxHeartbeats 32000000 in",
                  "theorem eleven_model_impossible {lam p : ℝ} (m : ElevenModel lam p) : False := by"]
        lines += self.setup(need)+body
        lines += ["", "#print axioms eleven_model_impossible", f"end {NS}"]
        return '\n'.join(lines)+'\n'


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def shape(node):
    if isinstance(node,int):return (0,0,1)
    if len(node)==4:
        f,b,l=shape(node[3])
        return (f+1,b,l+1)
    shapes=[shape(c) for c in node[1:]]
    return (sum(s[0] for s in shapes),1+sum(s[1] for s in shapes),sum(s[2] for s in shapes))


def freeze_write(path, source):
    if path.exists():
        assert path.read_text()==source, f'frozen source changed: {path}'
    else:
        path.write_text(source)


def compile_source(module):
    source=ROOT/'Jsp000404'/f'{module}.lean'
    output=ROOT/'.lake/build/lib/lean/Jsp000404'/f'{module}.olean'
    log=ROOT/'verification'/f'{module}_20261005.log'
    log.parent.mkdir(exist_ok=True)
    began=time.monotonic()
    with log.open('w') as handle:
        result=subprocess.run(['/usr/bin/time','-l','lake','env','lean','--trust=0','-o',str(output),str(source)],
                              cwd=ROOT,stdout=handle,stderr=subprocess.STDOUT)
    text=log.read_text()
    groups=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text,re.S)
    axioms=sorted({a.strip() for group in groups for a in group.split(',') if a.strip()})
    warnings=re.findall(r'^.*warning:.*$',text,re.M)
    peak=re.search(r'(\d+)\s+maximum resident set size',text)
    passed=result.returncode==0 and bool(groups) and not warnings and set(axioms)<={'propext','Classical.choice','Quot.sound'}
    return {'module':module,'exit_code':result.returncode,'status':'PASS' if passed else 'FAIL',
            'axioms':axioms,'seconds':round(time.monotonic()-began,3),'source_sha256':sha(source),
            'warnings':warnings,'maximum_resident_set_size_bytes':int(peak.group(1)) if peak else None,
            'log':str(log),'olean':str(output) if passed else None}


def verify_batch(report,jobs,rss_limit_gib):
    count=report['planned_shard_count']
    previous=report.get('kernel_verification',{})
    if not isinstance(previous,dict):previous={}
    allowed={'propext','Classical.choice','Quot.sound'}
    def valid(receipt):
        if not receipt or receipt.get('status')!='PASS' or receipt.get('exit_code')!=0:return False
        source=ROOT/'Jsp000404'/f"{receipt['module']}.lean"
        return (set(receipt.get('axioms',()))<=allowed and bool(receipt.get('axioms')) and
                not receipt.get('warnings') and receipt.get('olean') and Path(receipt['olean']).exists() and
                source.exists() and sha(source)==receipt['source_sha256'])
    receipts={r['number']:r for r in previous.get('completed_shards',[]) if valid(r)}
    probe=report.get('probe',{})
    if valid(probe.get('shard')):
        r=dict(probe['shard'])
        r['number']=probe['planned_shard_number']
        receipts[r['number']]=r
    model=previous.get('model') if valid(previous.get('model')) else probe.get('model')
    if not valid(model):model=compile_source('NoSatElevenDBMModel')
    verification={'status':'RUNNING','trust_level':0,'expected_shards':count,'model':model,
                  'maximum_parallel_jobs':jobs,'own_lean_rss_limit_gib':rss_limit_gib,
                  'maximum_observed_parallel_jobs':0,'maximum_observed_own_lean_rss_bytes':0,
                  'completed_shards':list(receipts.values()),'failed_shards':[],
                  'reused_verified_shards':len(receipts),'terminal':'NOT_RUN'}
    report['kernel_verification']=verification
    began=time.monotonic()
    def save():
        verification['elapsed_seconds']=round(time.monotonic()-began,3)
        verification['completed_shards'].sort(key=lambda r:r['number'])
        REPORT.write_text(json.dumps(report,indent=2)+'\n')
    if model['status']!='PASS':
        verification['status']='FAIL';save();return
    pending=iter(i for i in range(count) if i not in receipts)
    nominal_rss=int(1.7*1024**3)
    limit_rss=rss_limit_gib*1024**3
    def own_rss(numbers):
        output=subprocess.check_output(['ps','-axo','rss,command'],text=True)
        total=0;seen=set()
        for line in output.splitlines():
            fields=line.strip().split(maxsplit=1)
            if len(fields)!=2 or not fields[0].isdigit():continue
            command=fields[1]
            if command.split(maxsplit=1)[0].rsplit('/',1)[-1]!='lean':continue
            match=re.search(r'NoSatElevenDBMShard(\d+)\.lean',command)
            if match and int(match.group(1)) in numbers:
                total+=int(fields[0])*1024;seen.add(int(match.group(1)))
        verification['maximum_observed_own_lean_rss_bytes']=max(verification['maximum_observed_own_lean_rss_bytes'],total)
        return total+nominal_rss*(len(numbers)-len(seen))
    save()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures={}
        def dispatch():
            while len(futures)<jobs and not verification['failed_shards']:
                if own_rss(set(futures.values()))+nominal_rss>limit_rss:break
                number=next(pending,None)
                if number is None:break
                futures[pool.submit(compile_source,f'NoSatElevenDBMShard{number:03d}')]=number
                verification['maximum_observed_parallel_jobs']=max(verification['maximum_observed_parallel_jobs'],len(futures))
        dispatch()
        while futures:
            done,_=wait(futures,timeout=1.,return_when=FIRST_COMPLETED)
            own_rss(set(futures.values()))
            if not done:continue
            for future in done:
                number=futures.pop(future)
                receipt=future.result();receipt['number']=number
                key='completed_shards' if receipt['status']=='PASS' else 'failed_shards'
                verification[key].append(receipt)
                print(json.dumps({'kernel_progress':True,'shard':number,'status':receipt['status'],
                                  'seconds':receipt['seconds'],'rss_bytes':receipt['maximum_resident_set_size_bytes'],
                                  'completed':len(verification['completed_shards']),'of':count,
                                  'own_rss_peak_bytes':verification['maximum_observed_own_lean_rss_bytes']}),flush=True)
            save();dispatch()
    if len(verification['completed_shards'])==count and not verification['failed_shards']:
        verification['terminal']=compile_source('NoSatElevenDBMTerminal')
        verification['status']=verification['terminal']['status']
        if verification['status']=='PASS':
            report['diagnostic_only_until_kernel_checked']=False
            report['actual_geometry_consumers_verified']=False
    else:verification['status']='FAIL'
    save()
    print(json.dumps({'kernel_status':verification['status'],'completed_shards':len(verification['completed_shards']),
                      'terminal':verification['terminal'],'elapsed_seconds':verification['elapsed_seconds']}),flush=True)


def main():
    if not __debug__:raise RuntimeError('proof dependency checks require assertions enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-checks',type=int,default=300)
    parser.add_argument('--probe',action='store_true')
    parser.add_argument('--from-evidence',action='store_true')
    parser.add_argument('--generate-all',action='store_true')
    parser.add_argument('--verify-all',action='store_true')
    parser.add_argument('--jobs',type=int,default=3)
    parser.add_argument('--rss-limit-gib',type=float,default=6.)
    args=parser.parse_args()
    assert 1<=args.max_checks<=300
    assert 1<=args.jobs<=3 and 0<args.rss_limit_gib<=6
    assert not args.verify_all or args.generate_all
    began=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='jsp404_eleven_export_') as directory:
        if args.from_evidence:
            previous=json.loads(REPORT.read_text())
            assert sha(EVIDENCE)==previous['tree_evidence_sha256']
            assert sha(opt.__file__)==previous['frozen_search_sha256']
            assert sha(opt.audited.__file__)==previous['frozen_atom_source_sha256']
            with gzip.open(EVIDENCE,'rb') as handle:
                evidence=pickle.load(handle)
            search=opt.audited.Search(11,180.,600000,'tight')
            assert search.atoms==evidence['atoms'] and search.triples==evidence['triples']
            raw=evidence['raw_tree']
            search.stats=evidence['raw_stats']
        else:
            search=RecordingSearch(opt.build_native(directory),180.,600000,0,20.)
            raw=search.replay()
        diag=json.loads((ROOT/'research/JSP404_ELEVEN_DBM_OPTIMIZED_20261005.json').read_text())
        comparable=('nodes','leaves','max_depth','forced_splits','branch_splits','largest_cycle_core',
                    'closure_updates','redundant_triangles_removed','terminal_states','matrix_copies',
                    'forced_survivor_additions')
        assert all(search.stats[k]==diag[k] for k in comparable), 'replay differed from complete diagnostic'
        exporter=Exporter(search)
        exporter.audit(raw,exporter.base_mask)
        pruned=exporter.prune(raw,exporter.base_mask)
        exporter.audit(pruned,exporter.base_mask)
        meta=exporter.metadata[id(pruned)]
        assert meta['checks']==meta['forced']+meta['binary']+1
        raw_shape,pruned_shape=shape(raw),shape(pruned)
        assert raw_shape[1]==pruned_shape[1], 'a two-arm node was dropped'
        if not args.from_evidence:
            with gzip.open(EVIDENCE,'wb',compresslevel=6) as handle:
                pickle.dump({'atoms':search.atoms,'triples':search.triples,'raw_tree':raw,
                             'pruned_tree':pruned,'raw_stats':search.stats},handle,protocol=5)
        shards,cuts=exporter.plan(pruned,args.max_checks)
        sizes=[]
        for i,(node,incoming) in enumerate(shards):
            source=exporter.shard_source(i,node,incoming)
            sizes.append({'number':i,'checks':exporter.metadata[id(node)]['checks'],
                          'lines':len(source.splitlines()),'bytes':len(source.encode()),
                          'incoming_hypotheses':len(incoming)})
        model=exporter.model_source()
        terminal=exporter.terminal_source(pruned,shards,cuts)
        report={'diagnostic_only_until_kernel_checked':True,'result':'complete_pruned_proof_plan',
                'points':11,'atom_count':len(search.atoms),'atoms':search.atoms,
                'raw_replay_matches_diagnostic':{k:search.stats[k] for k in comparable},
                'raw_and_pruned_all_leaf_scopes_checked':True,
                'raw_structural_forced_nodes':raw_shape[0],
                'raw_structural_two_arm_nodes':raw_shape[1],
                'all_structural_two_arm_nodes_preserved':raw_shape[1]==pruned_shape[1],
                'pruning_rule':'Drop a forced step iff its pruned surviving proof needs no survivor atom; retain all binary arms.',
                'pruned_tree':{'split_nodes':meta['forced']+meta['binary'],'cycle_leaves':meta['checks'],
                               'forced_nodes':meta['forced'],'binary_nodes':meta['binary'],
                               'max_split_depth':meta['depth'],'removed_forced_nodes':exporter.removed_forced,
                               'root_needs_only_base_atoms':meta['need'] & ~exporter.base_mask == 0,
                               'used_base_atoms':(meta['need']&exporter.base_mask).bit_count()},
                'planned_shards':sizes,'planned_shard_count':len(shards),
                'max_checks_per_shard':args.max_checks,
                'planned_total_source_bytes':sum(s['bytes'] for s in sizes)+len(model.encode())+len(terminal.encode()),
                'planned_total_source_lines':sum(s['lines'] for s in sizes)+len(model.splitlines())+len(terminal.splitlines()),
                'planned_root_source_lines':len(terminal.splitlines()),
                'tree_evidence':str(EVIDENCE),'tree_evidence_sha256':sha(EVIDENCE),
                'source_sha256':sha(__file__),'frozen_search_sha256':sha(opt.__file__),
                'frozen_atom_source_sha256':sha(opt.audited.__file__),
                'reused_frozen_tree_evidence':args.from_evidence,
                'kernel_verification':'NOT_RUN','all_shards_generated':False,
                'elapsed_plan_seconds':round(time.monotonic()-began,3)}
        if args.from_evidence:
            for key in ('probe','kernel_verification','generated_sources'):
                if key in previous:report[key]=previous[key]
        REPORT.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k not in ('atoms','planned_shards')}),flush=True)
        if args.generate_all:
            generated=[]
            model_path=ROOT/'Jsp000404/NoSatElevenDBMModel.lean'
            freeze_write(model_path,model)
            generated.append({'module':'NoSatElevenDBMModel','source_sha256':sha(model_path)})
            for i,(node,incoming) in enumerate(shards):
                path=ROOT/'Jsp000404'/f'NoSatElevenDBMShard{i:03d}.lean'
                freeze_write(path,exporter.shard_source(i,node,incoming))
                generated.append({'module':f'NoSatElevenDBMShard{i:03d}','source_sha256':sha(path)})
            terminal_path=ROOT/'Jsp000404/NoSatElevenDBMTerminal.lean'
            freeze_write(terminal_path,terminal)
            generated.append({'module':'NoSatElevenDBMTerminal','source_sha256':sha(terminal_path)})
            report['generated_sources']=generated
            report['all_shards_generated']=True
            REPORT.write_text(json.dumps(report,indent=2)+'\n')
            print(json.dumps({'generated_frozen_sources':len(generated),'source_bytes':report['planned_total_source_bytes']}),flush=True)
        if args.verify_all:verify_batch(report,args.jobs,args.rss_limit_gib)
        if args.probe:
            # One model and one actual planned shard; a batch needs separate authorization.
            index=max(range(len(shards)),key=lambda i:sizes[i]['bytes'])
            node,incoming=shards[index]
            model_path=ROOT/'Jsp000404/NoSatElevenDBMModel.lean'
            shard_path=ROOT/'Jsp000404'/f'NoSatElevenDBMShard{index:03d}.lean'
            model_path.write_text(model)
            shard_path.write_text(exporter.shard_source(index,node,incoming))
            report['probe']={'planned_shard_number':index,'select_largest_planned_source':True,
                             'model':compile_source('NoSatElevenDBMModel')}
            REPORT.write_text(json.dumps(report,indent=2)+'\n')
            if report['probe']['model']['status']=='PASS':
                report['probe']['shard']=compile_source(f'NoSatElevenDBMShard{index:03d}')
            report['elapsed_total_seconds']=round(time.monotonic()-began,3)
            REPORT.write_text(json.dumps(report,indent=2)+'\n')
            print(json.dumps({'probe':report['probe'],'elapsed_total_seconds':report['elapsed_total_seconds']}),flush=True)


if __name__=='__main__':main()
