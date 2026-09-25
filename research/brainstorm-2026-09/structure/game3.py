import sys
import numpy as np
et=float(sys.argv[1]); ea=float(sys.argv[2]); es=float(sys.argv[3])
ys=np.linspace(0,1,201)
dirs=('left','right','same')
def h(prev,delta,side):
    if delta=='left': return 1.0 if prev=='R' else 0.0
    if delta=='right': return 1.0 if prev=='L' else 0.0
    return 1.0 if prev!=side else 0.0
def ecost(delta,side,y):
    d = y if side=='L' else 1-y
    if delta=='right': c = et if side=='L' else ea
    elif delta=='left': c = et if side=='R' else ea
    else: c = es
    return c*d
# one-step lookahead game: state (sigma_prev, delta); adversary picks y, delta'; we pick sigma
V={(s,d):0.0 for s in 'LR' for d in dirs}
for it in range(2000):
    Vn={}
    for (sp,d) in V:
        best=-1e9
        for y in ys:
            for d2 in dirs:
                v=min(h(sp,d,s)+ecost(d,s,y)+V[(s,d2)] for s in 'LR')
                best=max(best,v)
        Vn[(sp,d)]=best
    m=max(Vn.values()); gain=m-max(V.values()); V={k:v-m for k,v in Vn.items()}
print(et,ea,es,'one-step value',gain)
print({k:round(v,3) for k,v in V.items()})
