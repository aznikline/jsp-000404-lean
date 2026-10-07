# Numeric controls: actual projective rows, scores, potential, deletions.
import math, itertools
def rows(P):
    R=[]
    for i,(x,y) in enumerate(P):
        d=sorted((math.atan2(Y-y,X-x))%math.pi for j,(X,Y) in enumerate(P) if j!=i)
        R.append(d)
    return R
def gaps(d):
    g=[d[k+1]-d[k] for k in range(len(d)-1)]+[math.pi+d[0]-d[-1]]
    return g
def gs(lam,x): return max(0,math.floor(x/lam+1e-12)-1)
def score(lam,d): return sum(gs(lam,g) for g in gaps(d))
def legal(P,lam):
    for i,j,k in itertools.permutations(range(len(P)),3):
        a=[P[i][0]-P[j][0],P[i][1]-P[j][1]]; b=[P[k][0]-P[j][0],P[k][1]-P[j][1]]
        ang=math.acos(max(-1,min(1,(a[0]*b[0]+a[1]*b[1])/math.hypot(*a)/math.hypot(*b))))
        if ang>math.pi-lam+1e-12: return False
    return True
def scores(P,lam): return [score(lam,d) for d in rows(P)]
def pot(P,lam): return sum(2**k for k in scores(P,lam))
def hull(P):
    pts=sorted(range(len(P)),key=lambda i:P[i])
    def cr(o,a,b): return (P[a][0]-P[o][0])*(P[b][1]-P[o][1])-(P[a][1]-P[o][1])*(P[b][0]-P[o][0])
    lo=[];up=[]
    for i in pts:
        while len(lo)>=2 and cr(lo[-2],lo[-1],i)<=0: lo.pop()
        lo.append(i)
    for i in reversed(pts):
        while len(up)>=2 and cr(up[-2],up[-1],i)<=0: up.pop()
        up.append(i)
    return lo[:-1]+up[:-1]
def ext(P):  # exterior angle at each hull vertex = projective outside gap
    H=hull(P); m=len(H); out={}
    for t in range(m):
        a,b,c=P[H[t-1]],P[H[t]],P[H[(t+1)%m]]
        u=(b[0]-a[0],b[1]-a[1]); v=(c[0]-b[0],c[1]-b[1])
        out[H[t]]=math.atan2(u[0]*v[1]-u[1]*v[0],u[0]*v[0]+u[1]*v[1])
    return out
def report(name,P,lam):
    S=scores(P,lam); print(f"== {name}: N={len(P)} lam={lam:.4f} legal={legal(P,lam)} scores={S} potential={sum(2**k for k in S)}")
    E=ext(P); print("   hull exterior/lam:",{i:round(E[i]/lam,3) for i in E})
    Z=[i for i in E if S[i]==0]
    for q,r in itertools.combinations(Z,2):
        Q=[P[i] for i in range(len(P)) if i not in (q,r)]; idx=[i for i in range(len(P)) if i not in (q,r)]
        S2=scores(Q,lam); E2=ext(Q)
        cost=sum(2**S2[k]-2**S[idx[k]] for k in range(len(idx)))
        ev=[idx[k] for k in E2 if idx[k] in E and E2[k]>=(gs(lam,E[idx[k]])+2)*lam-1e-12]
        newh=[idx[k] for k in E2 if idx[k] not in E]
        turn=sum(E2[k]-E[idx[k]] for k in E2 if idx[k] in E)+sum(E2[k] for k in E2 if idx[k] not in E)
        print(f"   del {q},{r}: expense={cost} growthEvents={ev} exposed={newh} turning_check={turn:.6f} vs extq+extr={E[q]+E[r]:.6f}")
if __name__=="__main__":
    lam=math.pi/4; P=[(math.cos(2*math.pi*k/7),math.sin(2*math.pi*k/7)) for k in range(7)]
    report("Regular7 @pi/4",P,lam)
    report("F16 five-point @7pi/30",[(0,-1000),(-50,0),(-49,1),(49,1),(50,0)],7*math.pi/30)
    P=[(math.cos(2*math.pi*k/8),math.sin(2*math.pi*k/8)) for k in range(8)]
    report("Regular8 @pi/4",P,math.pi/4)
    report("Regular8+center @pi/4",P+[(0,0)],math.pi/4)
