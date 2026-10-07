# Like search2 but REQUIRE >=1 original interior point; also record exposure in zero-pair deletions.
import math, random, itertools, sys
sys.path.insert(0,'/home/ubuntu/work'); from controls import *
def expense(P,lam,S,rm):
    idx=[i for i in range(len(P)) if i not in rm]; Q=[P[i] for i in idx]
    S2=scores(Q,lam); return sum(2**S2[k]-2**S[idx[k]] for k in range(len(idx)))
def viol(P,lam):
    S=scores(P,lam); E=ext(P); Z=[i for i in range(len(P)) if S[i]==0]; HZ=[i for i in E if S[i]==0]
    v=max(0,2-len(HZ))*10 + max(0,1-(len(P)-len(E)))*10
    v+=sum(expense(P,lam,S,(z,)) for z in Z)
    v+=sum(max(0,expense(P,lam,S,(q,r))-1) for q,r in itertools.combinations(Z,2))
    return v,S
seed=int(sys.argv[1]); random.seed(seed)
for restart in range(300):
    lam=random.uniform(2*math.pi/9+0.005, math.pi/4)
    m=random.choice([5,6,7,8]); 
    P=[(math.cos(2*math.pi*j/m),math.sin(2*math.pi*j/m)) for j in range(m)]
    for t in range(3000):
        r=random.uniform(0.6,0.98); th=random.uniform(0,2*math.pi); x=(r*math.cos(th),r*math.sin(th))
        if legal(P+[x],lam): P.append(x); break
    if len(P)==m: continue
    v,S=viol(P,lam)
    for it in range(2500):
        i=random.randrange(len(P)); s=0.05*random.random()
        Q=list(P); Q[i]=(P[i][0]+random.gauss(0,s),P[i][1]+random.gauss(0,s))
        if not legal(Q,lam): continue
        v2,S2=viol(Q,lam)
        if v2<=v: P,v,S=Q,v2,S2
        if v==0: break
    if v==0:
        print("FOUND lam=%.6f N=%d F=%d S=%s hull=%s"%(lam,len(P),sum(2**x for x in S),S,hull(P)))
        print(" P=",[(round(x,6),round(y,6)) for x,y in P]); sys.stdout.flush()
print("done")
