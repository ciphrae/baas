A=3.5
def best(P,cap=None):
    c=(A/(3*P))**0.25
    if cap and c>cap: c=cap
    return c, A/c+P*c**3
for name,P in [("current",12.5),("drain only (A)",11.5),("displacement-charged Prep (E)",11.5-1.0),
               ("B + current Arr",4/3+1),("B + sideways Arr",4/3+1/3),("B + drain",4/3),
               ("B-loops/C + drain",2/3),("D + drain",1/3),("lower bound fixed arch",2/3)]:
    c1,v1=best(P,1.0); c2,v2=best(P)
    print(f"{name:32s} P={P:6.3f}  c<=1: c={c1:.3f} K={v1:.3f}   free c: c={c2:.3f} K={v2:.3f}")
# exact pairwise sums
for k in [4,8,16,64]:
    S=sum(abs(a-b) for a in range(k) for b in range(k))
    pair=2*k*k*S  # sum over y,i of |da|+|db|
    D=sum(b*(b-1) for b in range(k))  # per (group-col) vertical fill, times k*k*s^2
    print(k, pair/k**5, k*k*D/k**5)
