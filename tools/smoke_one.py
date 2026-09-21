import sys, time, itertools, importlib.util
spec = importlib.util.spec_from_file_location(
    'rc', 'tools/remainder_check.py')
rc = importlib.util.module_from_spec(spec)
sys.argv = ['x'] + sys.argv[1:]
spec.loader.exec_module(rc)

n = rc.N
ks = [3, 2, 2, 1]
VV = [rc.vertex_variants(v, ks[v],
                          tuple(x for x in range(4) if x != v), n)
      for v in range(4)]
sig = {}
for i in range(4):
    for j in range(4):
        if i == j:
            continue
        rem = sorted(k for k in range(4) if k != i and k != j)
        sig[(i, j)] = [
            (1 if vv['side'][(j, rem[0])] == 1 else 0) |
            (2 if vv['side'][(j, rem[1])] == 1 else 0)
            for vv in VV[i]]

def edge_ok(i, j, iv, jv):
    return sig[(i, j)][iv] == (3 - sig[(j, i)][jv])

mode = sys.argv[1] if len(sys.argv) > 1 else 'A'
sol = [None] * 4
soli = [-1] * 4
tested = [0]
done = [False]

def bt(i):
    if done[0]:
        return
    if i == 4:
        tested[0] += 1
        if tested[0] % 5000 == 0:
            print('  tested', tested[0], flush=True)
        if all(rc.tri_maybe(t, sol, n)
               for t in itertools.combinations(range(4), 3)):
            rc.ORIG.clear()
            b = rc.build_case(sol, n, mode)
            if b is None:
                return
            ineqs, eqs = b
            ineqs = rc.substitute(eqs, ineqs)
            t = time.time()
            res = rc.lp_min_delta(ineqs)
            print(f'leaf {tested[0]}: LP took '
                  f'{round(time.time()-t, 3)}s')
            print('result:', res[0],
                  f'minδ={res[1]}' if res[0] == 'bounded' else '')
            print('variant indices:', soli)
            if res[0] == 'bounded':
                out = rc.extract_cert(ineqs, res[2])
                if out is None:
                    print('cert extraction FAILED (neg weight)')
                else:
                    W, combo = out
                    print('cert:')
                    for cid, w in sorted(W.items()):
                        if w:
                            print(f'   {w} x [{rc.ORIG[cid][0]}]')
                    print('combined form:',
                          {str(k): v for k, v in combo.items()})
            done[0] = True
            return
        return
    for idx, vv in enumerate(VV[i]):
        if all(edge_ok(i, j, idx, soli[j]) for j in range(i)):
            sol[i] = vv
            soli[i] = idx
            bt(i + 1)
            sol[i] = None
            soli[i] = -1
            if done[0]:
                return

bt(0)
print('leaves tested:', tested[0], 'done:', done[0])
