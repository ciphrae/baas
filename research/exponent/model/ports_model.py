import math
from tree_model import tree_bound
# variants of the per-tile hop cost; everything else as in treeBound
def err(n,h,b,lam,variant,slack=1.0):
    q=h*b
    k=min(math.sqrt(n/(8*q*slack)), math.sqrt(n/(16*lam)))
    if b**h<k or k<2: return None
    s=n/k
    tb,d=tree_bound(k,q,s,h,lam)
    hops_cur=d['hops']
    if variant=='cur': return tb/n**2.5
    R=6*q*s+30*lam*k*q
    cross=2*(20*k*(q+2)+600*k+2000)          # distance-charged: O(kq) per tile per axis
    if variant=='dist':   # only the band-crossing charged by distance
        per=2*h*20*s+cross
    elif variant=='buf':  # buffer boxes at gateways + distance charge
        per=20*s+(2*h-1)*(20*math.sqrt(R)+20*q+50)+cross
    tb2=tb-hops_cur+per*n*n
    return tb2/n**2.5
def best(n,variant):
    lam=3*(math.floor(math.log2(n))+1)
    out=None
    for h in range(1,80):
        for b in [x/2 for x in range(4,600)]+list(range(300,3000,25)):
          for sl in [1,2,4,8,16,32]:
            e=err(n,h,b,lam,variant,sl)
            if e and (out is None or e<out[0]): out=(e,h,b,sl)
    return out
for L in [23,30,40,60,100,200]:
    n=2.0**L; ln=math.log(n)
    row=[]
    for v in ['cur','dist','buf']:
        e,h,b,sl=best(n,v)
        row.append(f"{v}: {e/ln**1.5:6.1f} {e/ln:7.1f} {e/ln**.5:7.1f} (h{h} b{b} x{sl})")
    print(f"2^{L:<4}","  ".join(row))
