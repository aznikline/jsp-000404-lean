import sys, time
sys.path.insert(0,'.')
import lane_e_util as le
import e2_util as e2
for d in [(0,0,1,4,4,5),(0,1,1,1,4,5)]:
    ks=le.ks_of_d(6,d)
    t=time.time(); found=0; stt=None
    for sdat,st in e2.guided(ks,6,6,mode='feas',max_sols=3,deadline=300):
        if sdat is None: stt=st; break
        v=e2.verify_candidate(sdat,6,6,d)
        print('d=%s FOUND cons=%s capped=%s relaxed=%s free=%s viol=%s'%(d,v['consistent'],v['capped'],v['relaxed'],v['free'],v['viol']),flush=True)
        found+=1
    print('d=%s done found=%d %.0fs stats=%s'%(d,found,time.time()-t,stt),flush=True)
