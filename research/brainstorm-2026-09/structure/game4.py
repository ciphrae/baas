import sys, itertools
import numpy as np
et,ea,es=map(float,sys.argv[1:4]); L=int(sys.argv[4])
ys=np.linspace(0,1,101)
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
# state: (prev side, tuple of L known deltas: current + L-1 future)
states=[(sp,ds) for sp in 'LR' for ds in itertools.product(dirs,repeat=L)]
V={st:0.0 for st in states}
# per state, adversary picks y (for current transfer) and new delta appended
for it in range(400):
    Vn={}
    for (sp,ds) in states:
        d=ds[0]
        best=-1e9
        for y in ys:
            # we choose side knowing y and ds; adversary then picks new delta
            v=min(h(sp,d,s)+ecost(d,s,y)+max(V[(s,ds[1:]+(dn,))] for dn in dirs) for s in 'LR')
            best=max(best,v)
        Vn[(sp,ds)]=best
    m=max(Vn.values()); gain=m-max(V.values()); V={k:v-m for k,v in Vn.items()}
print(et,ea,es,'lookahead',L,'value',round(gain,4))
