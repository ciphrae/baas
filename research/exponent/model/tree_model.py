import math
# treeBound (Tree/Transport.lean) with the budget inputs of FineLog.polynomial_budget_log
def tree_bound(k,q,s,h,lam, hop_first=None, hop_mid=None, hops_full=None):
    n=k*s
    lc=2*k*k*q*s
    nd=4*k*k*q*s+(14+30*lam)*k**3*q
    rv=6*k*k*q*s+(14+30*lam)*k**3*q+6*k*k
    hopK=20*s+20*k*(q+2)+600*k+2000
    if hop_mid is None:
        hops=hopK*2*h*n*n
    else:  # 2 full hops per tile (one per axis), 2(h-1) cheap ones
        hops=hopK*2*n*n + hop_mid*2*(h-1)*n*n
    run=lc*k*s + hops + k*s*(2*h+1)*nd + 3*(s+3)*(s*s*(15*k*k+30*k+18)+(14*k+18)*(lc+k*k))
    tb=2*n+52*n*rv+run+(26*n*(lc+nd+rv+lc+2*n+5)+k*k*(5*s**3+1509*s*s+1505*s+4796)+9354*k*k*n)/2
    return tb, dict(hops=hops, preload=52*n*rv, reloc=3*(s+3)*(s*s*(15*k*k+30*k+18)+(14*k+18)*(lc+k*k)),
                    stock=k*s*(2*h+1)*nd, lanes=lc*k*s, cleanfin=(26*n*(lc+nd+rv+lc)+5*k*k*s**3)/2)

def best(n, variant='cur', lamf=None):
    lam=3*(math.floor(math.log2(n))+1) if lamf is None else lamf(n)
    bestv=None
    for h in range(1,60):
        for b in [x/4 for x in range(8,2000,2)]:
            q=h*b
            # k from both constraints (continuous): 8kq<=s, 16k lam<=s, s=n/k
            k=min(math.sqrt(n/(8*q)), math.sqrt(n/(16*lam)))
            if k<2: continue
            # branching must realise k: b^h >= k  (continuous; b is per-level max)
            if b**h < k: continue
            s=n/k
            if variant=='cur': tb,_=tree_bound(k,q,s,h,lam)
            elif variant=='mid':  # intermediate hops cost O(k q) not O(s)
                tb,_=tree_bound(k,q,s,h,lam,hop_mid=20*k*(q+2)+600*k+2000+40*q)
            e=tb/n**2.5
            if bestv is None or e<bestv[0]: bestv=(e,h,b,k,q,lam)
    return bestv

if __name__=='__main__':
    for L in [23,30,40,60,100,200,400,800]:
        n=2.0**L
        ln=math.log(n)
        for v in ['cur','mid']:
            e,h,b,k,q,lam=best(n,v)
            print(f"2^{L:<4}{v:4} err/n^2.5={e:9.1f}  /ln^1.5={e/ln**1.5:7.2f} /ln^.5={e/ln**.5:8.2f}  h={h} b={b} q={q:.0f} lam={lam}")
