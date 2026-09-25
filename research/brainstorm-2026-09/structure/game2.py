import sys
import numpy as np
et=float(sys.argv[1]); ea=float(sys.argv[2]); es=float(sys.argv[3]) if len(sys.argv)>3 else ea
ys=np.linspace(0,1,41)
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
moves=[(d,y) for d in ('left','right','same') for y in ys]
Ds=np.linspace(-4,4,321)
def step(D,d,y):
    W={'L':D,'R':0.0}
    new={s:min(W[p]+h(p,d,s)+ecost(d,s,y) for p in 'LR') for s in 'LR'}
    m=min(new.values()); return m,new['L']-new['R']
V=np.zeros_like(Ds)
for it in range(300):
    Vn=np.array([max(g+np.interp(max(-4,min(4,D2)),Ds,V) for g,D2 in (step(D,d,y) for d,y in moves)) for D in Ds])
    gain=Vn.max()-V.max(); V=Vn-Vn.max()
print(et,ea,es,gain)
