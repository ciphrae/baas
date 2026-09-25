import numpy as np
N=2001; u=np.linspace(0,1,N)
f=4*np.minimum(u,1-u)+np.maximum(u,1-u)
print('E f (exit+home horizontal, return trick):',f.mean(),' max',f.max())
a=np.minimum(u,1-u)[:,None]; b=np.minimum(u,1-u)[None,:]
src=np.maximum(4*a, np.minimum(4*b, b+4*a))
print('vertical-carry option: E[source charge]',src.mean(),' total',src.mean()+0.75+0.75)
# constants
P=12.5
for A in (3.5,3.02,2.75,2.5):
    print('A',A,'constant',4/3*A**.75*(3*P)**.25, 'c',(2*A/75)**.25)
