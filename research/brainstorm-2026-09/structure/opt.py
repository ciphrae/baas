import numpy as np
from scipy.optimize import minimize
from game2 import game
P=12.5
gam={m:game(m,4.0,Y=201,iters=200)[0] for m in (1,2,3,4,5,6,8)}
print(gam)
def best(m, square=False):
    g=gam[m]
    if square:
        f=lambda z: np.exp(z[0])*(1+g)+P*m/np.exp(3*z[0])
        r=minimize(f,[0.5]); return r.fun, np.exp(r.x)
    f=lambda z: np.exp(z[0])+np.exp(z[1])*g+P*m/(np.exp(z[0])*np.exp(2*z[1]))
    r=minimize(f,[0.5,0.5]); return r.fun, np.exp(r.x)
for m in gam:
    print(m, 'square', best(m,True), 'rect', best(m))
