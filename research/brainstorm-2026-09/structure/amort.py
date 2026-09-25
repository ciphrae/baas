"""Horizontal/exit game with a position budget: each reservoir cell supplies at most
one extraction, so the source column y is (sub)uniform.  Upper bound via a prepaid
potential lam(y) >= 0:  total <= #T * Val(c - lam) + n^2 * mean(lam)."""
import numpy as np
from scipy.optimize import minimize
DIRS=('L','R','S')
Y=81; ys=np.linspace(0,1,Y)
def hcost(D,x,v):
    return x if D=='L' else (1-x if D=='R' else abs(x-v))
def val(lam, m=1, e=4.0, iters=150):
    V=np.linspace(0,1,m+1)
    vals={D:np.zeros(m+1) for D in DIRS}
    ex = e*np.abs(ys[:,None]-V[None,:]) - lam[:,None]
    for t in range(iters):
        new={}
        for D in DIRS:
            arr=np.empty(m+1)
            for xi,x in enumerate(V):
                h=np.array([hcost(D,x,v) for v in V])
                arr[xi]=max((h[None,:]+ex+vals[D2][None,:]).min(1).max() for D2 in DIRS)
            new[D]=arr
        g=max((new[D]-vals[D]).max() for D in DIRS)
        mn=min(new[D].min() for D in DIRS)
        vals={D:new[D]-mn for D in DIRS}
    return g
def lam_of(p):
    # symmetric piecewise-linear nonnegative potential with knots
    K=len(p); knots=np.linspace(0,0.5,K)
    half=np.interp(np.minimum(ys,1-ys),knots,np.abs(p))
    return half
def obj(p,m=1,e=4.0):
    lam=lam_of(p); return val(lam,m,e)+lam.mean()
if __name__=="__main__":
    for m,e in ((1,4.0),(1,3.0),(2,4.0)):
        print('m',m,'e',e,'no amort',val(np.zeros(Y),m,e))
        best=None
        for init in ([0,1,2,3,4,4],[0,.5,1,1.5,2,2],[0,2,4,4,4,4]):
            r=minimize(obj,np.array(init,float),args=(m,e),method='Nelder-Mead',options={'maxiter':600,'xatol':1e-3,'fatol':1e-4})
            if best is None or r.fun<best.fun: best=r
        print('  amortized upper bound',best.fun,'lam knots',np.round(np.abs(best.x),3))
