import itertools, sys
import numpy as np
# state: difference D = W(L)-W(R) of offline min cost; adversary maximizes growth.
e=float(sys.argv[1]) if len(sys.argv)>1 else 5.0
ys=np.linspace(0,1,41)
def h(prev,delta,side):
    if delta=='left': return 1.0 if prev=='R' else 0.0
    if delta=='right': return 1.0 if prev=='L' else 0.0
    return 1.0 if prev!=side else 0.0
moves=[(d,y) for d in ('left','right','same') for y in ys]
# value iteration: V(D) = max over moves [ growth + V(D') ], compute average via relative VI on grid of D
Ds=np.linspace(-3,3,241)
def step(D,d,y):
    W={'L':D,'R':0.0}
    new={}
    for s in 'LR':
        cost=e*(y if s=='L' else 1-y)
        new[s]=min(W[p]+h(p,d,s)+cost for p in 'LR')
    m=min(new.values())
    return m, new['L']-new['R']
V=np.zeros_like(Ds)
for it in range(400):
    Vn=np.full_like(Ds,-1e9)
    for a,D in enumerate(Ds):
        best=-1e9
        for d,y in moves:
            g,D2=step(D,d,y)
            D2=max(-3,min(3,D2))
            val=g+np.interp(D2,Ds,V)
            best=max(best,val)
        Vn[a]=best
    gain=Vn.max()-V.max()
    V=Vn-Vn.max()
print(e,gain)
