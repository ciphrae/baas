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
    stop_at = k * k * n if stop_frac is None else int(stop_frac * n * n)
    stats = {"V": 0, "H": 0, "Hbreak": 0, "reloc": 0, "Vdirect": 0}
    steps = 0

    def src_of(b, c, x, side):
        """band-b squares on the given side of column c with a class-(x,c) tile"""
        Js = range(0, c) if side == 0 else range(c + 1, k)
        g = x * k + c
        return [b * k + J for J in Js if cnt[b * k + J, g] > 0]

    # rotor state: insertions so far per (hub, side, class); traffic totals fixed at start
    traffic = {}
    for b in range(k):
        for c in range(k):
            for side in (0, 1):
                Js = range(0, c) if side == 0 else range(c + 1, k)
                t = np.zeros(k)
                for J in Js:
                    for x in range(k):
                        t[x] += cnt[b * k + J, x * k + c]
                traffic[(b, c, side)] = t
    done_ins = {key: np.zeros(k) for key in traffic}

    def hop1_copy(h):
        """hop1 into hub h; insertion class chosen by deficit round robin"""
        b, c = divmod(h, k)
        best = None
        for side in (0, 1):
            arr = rows[(b, c)][side]
            if len(arr) == 0: continue
            t = traffic[(b, c, side)]
            if t.sum() == 0: continue
            Js = range(0, c) if side == 0 else range(c + 1, k)
            for x in range(k):
                if t[x] == 0: continue
                if not any(cnt[b * k + J, x * k + c] > 0 for J in Js): continue
                # deficit: how far behind its share this (side, class) is
                frac = (done_ins[(b, c, side)][x] + 1) / t[x]
                if best is None or frac < best[0]:
                    best = (frac, side, x)
        if best is None:
            return None
        _, side, x = best
        Js = range(0, c) if side == 0 else range(c + 1, k)
        srcs = [b * k + J for J in Js if cnt[b * k + J, x * k + c] > 0]
        # rotor over sources too: take the one with most tiles of that class
        S = max(srcs, key=lambda q: cnt[q, x * k + c])
        done_ins[(b, c, side)][x] += 1
        J = S % k
        arr = rows[(b, c)][side]
        dist = (c - 1 - J) if J < c else (J - c - 1)
        p = min(dist * s + rng.randrange(s), len(arr) - 1)
        F = int(arr[0])
        arr[0:p] = arr[1:p + 1]
        arr[p] = x
        cnt[S, x * k + c] -= 1
        cnt[h, F * k + c] += 1
        stats["H"] += 1
        return S

    while True:
        steps += 1
        if steps > 10 * n * n:
            return None
        D = X
        a, c = divmod(D, k)
        # 1. hop2 from a hub in column c with class-D stock, then hop1 into that hub
        hubs = [b * k + c for b in range(k) if b != a and cnt[b * k + c, D] > 0]
        rng.shuffle(hubs)
        hubs.sort(key=lambda h: -cnt[h, D])
        done = False
        for h in hubs:
            cnt[h, D] -= 1; cnt[D, D] += 1
            S = hop1_copy(h)
            if S is not None:
                stats["V"] += 1; X = S; done = True; break
            # hub has no hop1 sources left: the blank stays at h (plain hop2)
            stats["Vdirect"] += 1; X = h; done = True; break
        if done: continue
        # 2. hop1 into D itself
        S = hop1_copy(D)
        if S is not None:
            X = S; continue
        # 3. stuck
        if misplaced() <= stop_at:
            break
        colD = cnt[:, D].copy(); colD[D] = 0
        cand = np.flatnonzero(colD > 0)
        if len(cand):
            S = int(cand[rng.randrange(len(cand))])
            cnt[S, D] -= 1; cnt[D, D] += 1; X = S; stats["reloc"] += 1
            continue
        rowsum = cnt.sum(axis=1) - np.diag(cnt); rowsum[D] = 0
        Zs = np.flatnonzero(rowsum > 0)
        if len(Zs) == 0: break
        Z = int(Zs[rng.randrange(len(Zs))])
        gs = [g for g in np.flatnonzero(cnt[Z] > 0) if g != Z]
        g = int(gs[rng.randrange(len(gs))])
        cnt[Z, g] -= 1; cnt[D, g] += 1; X = Z; stats["reloc"] += 1
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
                tr = st["H"] + st["Hbreak"] + st["V"] + st["Vdirect"]
                print(f"{kind:9s} k={k:2d} s={s:3d} n={n:4d} m={m:3d} hops/n2={tr/n**2:.3f} "
                      f"brk={st['Hbreak']/n**2:.3f} relocs={st['reloc']:6d} relocs*k/n2={st['reloc']*k/n**2:.4f} left/(k^2 n)={left/(k*k*n):.2f}",
                      flush=True)
