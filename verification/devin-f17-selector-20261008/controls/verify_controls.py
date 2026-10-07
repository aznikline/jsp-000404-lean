"""High-precision (mpmath, 50 digits) replay of numeric controls for
research/DEVIN_F17_SELECTOR_20261008.md. Coordinates are exact decimals.
Reports: band, legality slack, scores, potential, every single and pair
zero-deletion expense, hull exterior angles, boundary events, exposure,
turning identity, and the minimum floor margin (distance of gap/lam to an
integer) so that rounding cannot flip any floor. PAPER evidence only."""
from mpmath import mp, mpf, atan2, acos, pi, floor, sqrt, cos, sin
import itertools, sys
mp.dps = 50
def rows(P): return [sorted((atan2(Y-y, X-x)) % pi for j,(X,Y) in enumerate(P) if j != i) for i,(x,y) in enumerate(P)]
def gaps(d): return [d[k+1]-d[k] for k in range(len(d)-1)] + [pi+d[0]-d[-1]]
def gs(lam,g): return max(0, int(floor(g/lam))-1)
def sc(P,lam): return [sum(gs(lam,g) for g in gaps(d)) for d in rows(P)]
def fm(P,lam): return min(min(g/lam-floor(g/lam), floor(g/lam)+1-g/lam) for d in rows(P) for g in gaps(d))
def legal_slack(P,lam):
    m = mpf(10)
    for i,j,k in itertools.permutations(range(len(P)),3):
        a=(P[i][0]-P[j][0],P[i][1]-P[j][1]); b=(P[k][0]-P[j][0],P[k][1]-P[j][1])
        m=min(m, pi-lam-acos((a[0]*b[0]+a[1]*b[1])/sqrt(a[0]**2+a[1]**2)/sqrt(b[0]**2+b[1]**2)))
    return m
def hull(P):
    pts=sorted(range(len(P)),key=lambda i:P[i])
    cr=lambda o,a,b:(P[a][0]-P[o][0])*(P[b][1]-P[o][1])-(P[a][1]-P[o][1])*(P[b][0]-P[o][0])
    lo=[];up=[]
    for i in pts:
        while len(lo)>=2 and cr(lo[-2],lo[-1],i)<=0: lo.pop()
        lo.append(i)
    for i in reversed(pts):
        while len(up)>=2 and cr(up[-2],up[-1],i)<=0: up.pop()
        up.append(i)
    return lo[:-1]+up[:-1]
def ext(P):
    H=hull(P); m=len(H); out={}
    for t in range(m):
        a,b,c=P[H[t-1]],P[H[t]],P[H[(t+1)%m]]
        u=(b[0]-a[0],b[1]-a[1]); v=(c[0]-b[0],c[1]-b[1])
        out[H[t]]=atan2(u[0]*v[1]-u[1]*v[0],u[0]*v[0]+u[1]*v[1])
    return out
def report(name, P, lam):
    P=[(mpf(x),mpf(y)) for x,y in P]; lam=mpf(lam); S=sc(P,lam); E=ext(P)
    print(f"== {name}\n N={len(P)} lam={mp.nstr(lam,12)} band(2pi/9<lam<=pi/4)={2*pi/9<lam<=pi/4}"
          f" legality_slack={mp.nstr(legal_slack(P,lam),6)} scores={S} potential={sum(2**k for k in S)}"
          f" floor_margin={mp.nstr(fm(P,lam),4)}")
    print(" hull exterior/lam:", {i: mp.nstr(E[i]/lam,5) for i in E}, "interior:", [i for i in range(len(P)) if i not in E])
    Z=[i for i in range(len(P)) if S[i]==0]; worst1=0; worst2=0
    for r in (1,2):
        for rm in itertools.combinations(Z,r):
            idx=[i for i in range(len(P)) if i not in rm]; Q=[P[i] for i in idx]; S2=sc(Q,lam); E2=ext(Q)
            ex=sum(2**S2[k]-2**S[idx[k]] for k in range(len(idx)))
            ev=[idx[k] for k in E2 if idx[k] in E and E2[k] >= (gs(lam,E[idx[k]])+2)*lam]
            expo=[idx[k] for k in E2 if idx[k] not in E]
            line=f"  delete {rm}: expense={ex} events={ev} exposed={expo} floor_margin={mp.nstr(fm(Q,lam),4)}"
            if r==2 and all(i in E for i in rm):
                turn=sum(E2[k]-E[idx[k]] for k in E2 if idx[k] in E)+sum(E2[k] for k in E2 if idx[k] not in E)
                line+=f" turning_residual={mp.nstr(turn-E[rm[0]]-E[rm[1]],3)}"
            print(line)
            if r==1: worst1=max(worst1,ex)
            else: worst2=max(worst2,ex)
    print(f" max single-zero expense={worst1}  max zero-pair expense={worst2}")
if __name__=="__main__":
    report("Regular7 @ pi/4 (low-potential control)", [(cos(2*pi*k/7),sin(2*pi*k/7)) for k in range(7)], pi/4)
    report("F16 five-point @ 7pi/30", [(0,-1000),(-50,0),(-49,1),(49,1),(50,0)], 7*pi/30)
    report("C8: all-hull all-zero, local zero ledgers hold", [('1.070306','-0.002983'),('0.800676','0.654199'),('0.047225','0.974002'),('-0.71686','0.679073'),('-1.007279','0.03282'),('-0.72367','-0.651014'),('-0.007559','-0.960985'),('0.77141','-0.66762')], '0.764683')
    report("C6: all-hull, two score-one points, local zero ledgers hold", [('1.125417','-0.322256'),('0.873151','0.883193'),('-0.882418','0.751913'),('-0.904372','0.140471'),('0.02741','-0.959508'),('0.340591','-0.969721')], '0.709937')
    for extra in sys.argv[1:]:
        import ast; nm,lam,P=ast.literal_eval(open(extra).read()); report(nm,P,lam)
