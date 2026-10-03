import z3, itertools, json, os

P = 5
delta = z3.Real('delta')
t = [z3.Real(f't{i}') for i in range(P)]
d = {(i,j): z3.Real(f'd{i}{j}') for i in range(P) for j in range(i+1,P)}
def D(i,j): return d[(min(i,j),max(i,j))]

base = [z3.And(0 <= delta, delta < 1)]
for i in range(P-1): base.append(t[i] < t[i+1])
base += [0 <= t[0], t[P-1] <= delta]
p = 3 + delta
for i in range(P):
    for j in range(i+1,P):
        base += [t[i]+1 <= d[(i,j)], d[(i,j)] <= p-1+t[j]]

trips = {}
for i,j,k in itertools.combinations(range(P),3):
    trips[(i,j,k)] = z3.Or(
        z3.And(d[(i,j)]+1 <= d[(j,k)], d[(i,j)] < d[(i,k)], d[(i,k)] < d[(j,k)]),
        z3.And(d[(j,k)]+1 <= d[(i,j)], d[(j,k)] < d[(i,k)], d[(i,k)] < d[(i,j)]))

def leaf_smt(s, rowi, perm, gpos, use_trips):
    s.push()
    for c in base: s.add(c)
    for nm in use_trips: s.add(trips[tuple(int(x) for x in nm.strip("()").split(","))])
    chords = sorted([j for j in range(P) if j != rowi])
    cvars = [D(rowi,j) for j in chords]
    r = [cvars[perm[k]] for k in range(4)]
    gaps = [r[0]-t[rowi], r[1]-r[0], r[2]-r[1], r[3]-r[2], t[rowi]+p-r[3]]
    for k in range(3): s.add(r[k] <= r[k+1])
    s.add(z3.And(2 <= gaps[gpos], gaps[gpos] < 3))
    for g in range(5):
        if g != gpos: s.add(z3.And(0 <= gaps[g], gaps[g] < 2))
    res = s.check()
    s.pop()
    return res

HERE = os.path.dirname(os.path.abspath(__file__))
cores = json.load(open(os.path.join(HERE, 'n3_leaf_cores.json')))
s = z3.Solver(); s.set("timeout", 30000)
mincores = {}
for rowi in ['0','1','3','4']:
    rc = {}
    for key, core in cores[rowi].items():
        if core == 'SAT': rc[key] = 'SAT'; continue
        perm = tuple(int(x) for x in key.split(':')[0].strip('()').split(','))
        gpos = int(key.split(':')[1])
        cur = list(core)
        # greedy shrink
        improved = True
        while improved:
            improved = False
            for c in list(cur):
                cand = [x for x in cur if x != c]
                if leaf_smt(s, int(rowi), perm, gpos, cand) == z3.unsat:
                    cur = cand; improved = True; break
        rc[key] = cur
    mincores[rowi] = rc
json.dump(mincores, open(os.path.join(HERE, 'n3_leaf_min_cores.json'), 'w'))
import collections
for r in ['0','1','3','4']:
    print(r, collections.Counter(str(len(v)) for v in mincores[r].values() if v!='SAT'),
          'max:', max(len(v) for v in mincores[r].values() if v!='SAT'))
