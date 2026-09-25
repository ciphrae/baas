"""Exit-and-restore variant: after the exit the blank walks back to the source
tile's original cell, so reservoir columns are invariant.  State x = blank column.
Adversary picks direction D and next source column y (budget: y uniform over
reservoir cells, each cell at most once); we pick the exit side v in {0,1}.
Upper bound = min_lam [Val(c - lam) + mean(lam)], lam >= 0."""
import numpy as np
from scipy.optimize import minimize
Y=101; ys=np.linspace(0,1,Y)
def costs(e_face):
    # C[D][xi, yi] = min over v of cost; x grid = ys
    x=ys[:,None]; y=ys[None,:]
    L=x+np.minimum(4*y, e_face*(1-y))          # source left: facing side is right (v=1)
    R=(1-x)+np.minimum(4*(1-y), e_face*y)
    S=np.minimum(x+4*y, (1-x)+4*(1-y))
    return [L,R,S]
def val(lam,C,iters=300):
    h=np.zeros(Y)
    for t in range(iters):
        M=np.max([c - lam[None,:] + h[None,:] for c in C],axis=0)  # x by y
        new=M.max(1)
        g=(new-h).max(); h=new-new.min()
    return g
def lam_of(p):
    knots=np.linspace(0,1,len(p)); return np.interp(ys,knots,np.abs(p))
def bound(C,K=9):
    best=None
    for init in (np.zeros(K), np.linspace(0,2,K), 2*np.minimum(np.linspace(0,1,K),1-np.linspace(0,1,K))*2):
        r=minimize(lambda p: val(lam_of(p),C)+lam_of(p).mean(), init, method='Powell',options={'maxiter':4000,'xtol':1e-3,'ftol':1e-5})
        if best is None or r.fun<best.fun: best=r
    return best.fun, np.round(np.abs(best.x),3)
for e in (4.0,3.0):
    C=costs(e)
    print('e_face',e,'per-step worst',val(np.zeros(Y),C),' budget bound',bound(C))
    for name,c in zip('LRS',C):
        print('   only',name,'per-step',val(np.zeros(Y),[c]),'budget',bound([c])[0])
