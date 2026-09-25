"""Randomized two-hop Algorithm 4 (count model, exact rows as delay lines).

Blank at D=(a,c).  Candidates: squares S != D holding a tile T of class D.
  - S = (a, J):   hop1 into D along R(a,c): T enters the row, the row's head
                  (a column-c tile of arbitrary band) drops into D.
  - S = (b, c):   hop2 from S down/up C(c,a): D receives a class-D tile.
  - otherwise:    hop2 from hub h=(b,c) (needs a class-D tile in h: stock),
                  then hop1 into h along R(b,c): T enters the row, head -> h.
Blank moves to S.  S is chosen at random, weighted by its number of class-D
tiles, among valid candidates.  No valid candidate -> relocation (a direct
carry, cost ~n).

Rows start with the composition of their future traffic (random order), taken
from that traffic; seeds: m tiles of each class that uses hub h, taken from
that class's band-b sources (their hop1 done early).
"""
import sys, random
import numpy as np
from hubrun import make_perm


def setup(k, s, kind, seed):
    rng = random.Random(seed)
    n = k * s
    perm = make_perm(n, s, kind, rng)
    K = k * k
    cnt = np.zeros((K, K), dtype=np.int64)
    X = None
    for (r, c), (tr, tc) in perm.items():
        g = (tr // s) * k + tc // s
        q = (r // s) * k + c // s
        if (tr, tc) == (n - 1, n - 1):
            X = q; continue
        cnt[q, g] += 1
    return rng, n, cnt, X


def run(k, s, kind, m=4, seed=0, stop_frac=None, verbose=False):
    rng, n, cnt, X = setup(k, s, kind, seed)
    K = k * k
    band = np.arange(K) // k
    col = np.arange(K) % k
    nprng = np.random.default_rng(seed)

    def take_from_band(b, c, a, num):
        """remove up to num tiles of class (a,c) from band-b squares outside column c"""
        g = a * k + c
        got = 0
        order = [b * k + J for J in range(k) if J != c]
        rng.shuffle(order)
        for q in order:
            t = min(num - got, cnt[q, g])
            if t > 0:
                cnt[q, g] -= t; got += t
            if got == num: break
        return got

    # rows: per hub (b,c), sides L (left of block c) and R
    rows = {}
    for b in range(k):
        for c in range(k):
            sides = []
            for side in (0, 1):
                L = c * s if side == 0 else (k - 1 - c) * s
                Js = range(0, c) if side == 0 else range(c + 1, k)
                traffic = np.zeros(k, dtype=np.int64)
                for J in Js:
                    q = b * k + J
                    for a in range(k):
                        traffic[a] += cnt[q, a * k + c]
                tot = traffic.sum()
                bands = []
                if tot > 0 and L > 0:
                    want = np.floor(L * traffic / tot).astype(int)
                    for a in range(k):
                        got = take_from_band(b, c, a, int(want[a]))
                        bands += [a] * got
                # fill the rest with cyclic junk-free placeholders: column-c tiles from anywhere
                while len(bands) < L:
                    a = (len(bands) + b) % k
                    g = a * k + c
                    src = np.flatnonzero(cnt[:, g] > 0)
                    src = [q for q in src if col[q] != c] or [q for q in src if q != g]
                    if not src:
                        a = rng.randrange(k); bands.append(a); continue
                    cnt[src[0], g] -= 1; bands.append(a)
                rng.shuffle(bands)
                sides.append(np.array(bands, dtype=np.int32))
            rows[(b, c)] = sides
    # seeds
    for b in range(k):
        for c in range(k):
            h = b * k + c
            for a in range(k):
                if a == b: continue
                got = take_from_band(b, c, a, m)
                cnt[h, a * k + c] += got

    def hop1(h, S):
        """hop1 into hub h from source S: returns class delivered into h"""
        b, c = divmod(h, k)
        J = S % k
        side = 0 if J < c else 1
        arr = rows[(b, c)][side]
        dist = (c - 1 - J) if J < c else (J - c - 1)
        p = dist * s + rng.randrange(s)
        F = int(arr[0])
        arr[0:p] = arr[1:p + 1]
        return F, arr, p

    misplaced = lambda: int(cnt.sum() - np.trace(cnt))
    if stop_frac is None:
        stop_at = k * k * n
    else:
        stop_at = int(stop_frac * n * n)
    stats = {"H": 0, "V": 0, "HV": 0, "reloc": 0}
    mp = misplaced()
    steps = 0
    while True:
        steps += 1
        if steps > 10 * n * n:
            return None
        D = X
        a, c = divmod(D, k)
        colD = cnt[:, D].copy()
        colD[D] = 0
        cand = np.flatnonzero(colD > 0)
        valid = []
        weights = []
        for S in cand:
            bS, JS = divmod(int(S), k)
            if bS == a or JS == c:
                valid.append(int(S)); weights.append(colD[S])
            else:
                h = bS * k + c
                if cnt[h, D] > 0:
                    valid.append(int(S)); weights.append(colD[S])
        if not valid:
            if mp <= stop_at:
                break
            if len(cand):
                S = int(cand[rng.randrange(len(cand))])
                cnt[S, D] -= 1; cnt[D, D] += 1; X = S; stats["reloc"] += 1; mp -= 1
                continue
            # D complete: move blank to a square with work (foreign relocation)
            rowsum = cnt.sum(axis=1) - np.diag(cnt)
            rowsum[D] = 0
            Zs = np.flatnonzero(rowsum > 0)
            if len(Zs) == 0:
                break
            Z = int(Zs[rng.randrange(len(Zs))])
            gs = [g for g in np.flatnonzero(cnt[Z] > 0) if g != Z]
            g = int(gs[rng.randrange(len(gs))])
            cnt[Z, g] -= 1; cnt[D, g] += 1; X = Z; stats["reloc"] += 1
            continue
        w = np.array(weights, dtype=float)
        S = valid[int(nprng.choice(len(valid), p=w / w.sum()))]
        bS, JS = divmod(S, k)
        if JS == c:  # hop2 direct
            cnt[S, D] -= 1; cnt[D, D] += 1; mp -= 1; stats["V"] += 1
        elif bS == a:  # hop1 into D
            cnt[S, D] -= 1
            F, arr, p = hop1(D, S)
            arr[p] = a
            cnt[D, F * k + c] += 1
            mp -= 1
            if F != a: mp += 1
            stats["H"] += 1
        else:
            h = bS * k + c
            cnt[h, D] -= 1; cnt[D, D] += 1
            cnt[S, D] -= 1
            F, arr, p = hop1(h, S)
            arr[p] = a
            cnt[h, F * k + c] += 1
            # h: lost class D (misplaced) gained class F (misplaced unless F == bS)
            mp -= 1
            if F == bS: mp -= 1
            stats["HV"] += 1
        X = S
    return stats, n, misplaced()


if __name__ == "__main__":
    kinds = sys.argv[1].split(",")
    ks = [tuple(map(int, x.split("x"))) for x in sys.argv[2].split(",")]
    ms = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [4]
    for kind in kinds:
        for k, s in ks:
            for m in ms:
                r = run(k, s, kind, m)
                if r is None:
                    print(kind, k, s, m, "no termination", flush=True); continue
                st, n, left = r
                tr = st["H"] + st["V"] + 2 * st["HV"]
                print(f"{kind:9s} k={k:2d} s={s:3d} n={n:4d} m={m:3d} hops/n2={tr/n**2:.3f} "
                      f"relocs={st['reloc']:6d} relocs*k/n2={st['reloc']*k/n**2:.4f} left/(k^2 n)={left/(k*k*n):.2f}",
                      flush=True)
