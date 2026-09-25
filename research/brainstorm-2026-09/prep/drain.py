# Abstract drain run: squares (band,col), group x = square x. Edge x->z (mult s) for each
# V(z,x) cell (z != x). Round d = |band(z)-band(x)|, processed d = k-1..0, then H round.
# Greedy walk: at x pick an available out-edge (farthest-first is automatic per round);
# when stuck, relocate blank. Count relocations and check balance.
import random
def run(k,s,seed=0):
    rnd=random.Random(seed)
    sq=[(a,b) for a in range(k) for b in range(k)]
    relocs=0; blank=rnd.choice(sq)
    for d in range(k-1,-1,-1):
        out={x:[] for x in sq}
        for x in sq:
            for z in sq:
                if z!=x and abs(z[0]-x[0])==d: out[x]+= [z]*s
        indeg={z:0 for z in sq}
        for x in sq:
            for z in out[x]: indeg[z]+=1
        assert all(len(out[x])==indeg[x] for x in sq), "unbalanced"
        for x in sq: rnd.shuffle(out[x])
        while any(out[x] for x in sq):
            if not out[blank]:
                relocs+=1; blank=rnd.choice([x for x in sq if out[x]])
            blank=out[blank].pop()
    return relocs
for k in [3,4,6,8]:
    print(k, [run(k,5,seed) for seed in range(3)], "bound k^2*k =",k**3)
