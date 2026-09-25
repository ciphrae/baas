"""'Matched-exchange' transport with k^2 n corridor tiles (spatial row model).

Corridors: row R(a',c) in band a' (length n) holds tiles whose target column
block is c; column C(c,a) in strip c holds group (a,c) only (pass-through).
Transfer into blank square X=(a,c) (Zhong's count run, source Y=(a',b') holding
a group-X tile T):
  blank: X -> up/down C(c,a) to band a' -> into R(a',c) inside block c, where a
  band-a tile F (hence group (a,c)) is picked up at carry distance <= s
  -> along R(a',c) to T's column in block b' -> T enters the row.
  F goes down C(c,a) into X.  Row R(a',c) loses F, gains T (same group), and the
  row segment between F and T shifts one cell toward c.
We track rows exactly (as arrays of target bands) and count 'misses': transfers
where no source band a' has a group-X tile inside block c of R(a',c); then we
fetch F from outside block c and record the extra distance.
"""
import random, sys
import numpy as np
from collections import Counter
from rook_run import make_board

def run(k, s, kind, seed=0):
    rng = random.Random(seed)
    sq, X, n = make_board(k, s, kind, rng)
    # stock rows: R[(a',c)] = array of target bands (group (band,c)), cyclic pattern,
    # tiles taken from reservoirs (prefer non-home, else home)
    R = {}
    for ap in range(k):
        for c in range(k):
            row = np.array([(i + ap) % k for i in range(n)], dtype=np.int16)
            R[(ap, c)] = row
            for x in Counter(row.tolist()).items():
                band, cnt = x; g = (band, c)
                for Y in sorted(sq, key=lambda Y: (Y == g, abs(Y[0] - ap))):
                    t = min(cnt, sq[Y][g] - (1 if Y == g else 0))
                    if t > 0: sq[Y][g] -= t; cnt -= t
                    if cnt == 0: break
    transfers = misses = 0; extra = 0
    holders = {}  # group -> Counter of squares holding it (non-home)
    for Y, C in sq.items():
        for g, v in C.items():
            if v and g != Y: holders.setdefault(g, Counter())[Y] += v
    while True:
        a, c = X
        H = holders.get(X)
        if not H or sum(H.values()) == 0:
            # Zhong's rule: pick a different X?  In Algorithm 4 this means done for X;
            # the run ends when no square misses anything.
            left = [g for g, h in holders.items() if sum(h.values())]
            if not left: break
            # (should only happen at the very end) relocate blank to a holder square
            g = left[0]; Y = next(Y for Y, v in holders[g].items() if v)
            sq[Y][g] -= 1; sq[g][g] += 1; holders[g][Y] -= 1; X = Y; misses += 1; extra += n
            continue
        blk = slice(c * s, (c + 1) * s)
        best = None
        for Y, v in H.items():
            if not v: continue
            ap, bp = Y
            seg = R[(ap, c)][blk]
            hit = np.flatnonzero(seg == a)
            if hit.size:
                best = (0, Y, c * s + int(hit[0])); break
            # distance to nearest band-a tile outside block c
            idx = np.flatnonzero(R[(ap, c)] == a)
            if idx.size:
                d = int(np.min(np.minimum(np.abs(idx - c * s), np.abs(idx - (c + 1) * s + 1))))
                if best is None or d < best[0]: best = (d, Y, int(idx[np.argmin(np.minimum(np.abs(idx - c * s), np.abs(idx - (c + 1) * s + 1)))]))
        if best is None:
            sys.exit("row pools exhausted for a band")
        d, Y, pF = best
        if d: misses += 1; extra += d
        ap, bp = Y
        row = R[(ap, c)]
        pT = bp * s + rng.randrange(s)   # T's column
        # remove F at pF, shift segment between pF and pT toward pF, insert T (band a) at pT
        if pT > pF:
            row[pF:pT] = row[pF + 1:pT + 1].copy()
        elif pT < pF:
            row[pT + 1:pF + 1] = row[pT:pF].copy()
        row[pT] = a
        sq[Y][X] -= 1; sq[X][X] += 1; H[Y] -= 1
        X = Y; transfers += 1
    return transfers, misses, extra, n

if __name__ == "__main__":
    for kind in ["random", "transpose", "rot90", "rot180", "diagshift"]:
        for k in [3, 4, 5]:
            s = k * k
            t, m, e, n = run(k, s, kind)
            print(f"{kind:9s} k={k} s={s} n={n:4d} transfers/n^2={t/n**2:.3f} misses={m} "
                  f"miss-rate={m/max(t,1):.4f} extra/(n^2 s)={e/(n*n*s):.4f}", flush=True)
