"""Two-hop transport with hub reservoirs as buffers (count model, exact rows).

k x k squares of side s, n = k*s.  Class of a tile = its target square (a, c).
  hop1 (horizontal): into X=(b,J) from Y=(b,J'), a tile T with target column J.
      The blank runs along row R(b,J) (band b, holds tiles with target column J,
      any band) from block J to T's column; T enters the row there, the row
      segment shifts one cell toward J, and the row's end tile F (inside block J)
      drops into X's reservoir.  F's band is whatever the row holds: it is NOT T.
  hop2 (vertical): into X=(a,c) from a hub Y=(b',c) whose reservoir holds a
      tile of class X.  Column C(c,a) holds class X only, so it delivers class X
      into X and takes the extracted tile.  (Content invariant: not modelled.)
Rows are exact arrays (delay lines).  Hub reservoirs are random access.
Seeds: m tiles of each class (a,c) placed in every hub (b,c) of column c.
Stuck -> relocation (one O(n) carry): counted.
"""
import random, sys
import numpy as np
from collections import Counter


def make_perm(n, s, kind, rng):
    cells = [(r, c) for r in range(n) for c in range(n)]
    if kind == "random":
        tgt = cells[:]; rng.shuffle(tgt); return dict(zip(cells, tgt))
    if kind == "transpose":
        return {(r, c): (c, r) for (r, c) in cells}
    if kind == "rot90":
        return {(r, c): (c, n - 1 - r) for (r, c) in cells}
    if kind == "rot180":
        return {(r, c): (n - 1 - r, n - 1 - c) for (r, c) in cells}
    if kind == "diagshift":
        return {(r, c): ((r + s) % n, (c + s) % n) for (r, c) in cells}
    if kind == "quadswap":  # TL <-> BR, TR and BL fixed (block level)
        h = n // 2
        def f(r, c):
            if r < h and c < h: return (r + h, c + h)
            if r >= h and c >= h: return (r - h, c - h)
            return (r, c)
        return {p: f(*p) for p in cells}
    if kind == "blockperm":  # random permutation of squares, rigid
        k = n // s
        sqs = [(a, b) for a in range(k) for b in range(k)]
        img = sqs[:]; rng.shuffle(img); m = dict(zip(sqs, img))
        def f(r, c):
            A, B = m[(r // s, c // s)]
            return (A * s + r % s, B * s + c % s)
        return {p: f(*p) for p in cells}
    if kind == "bandcol":  # band b -> column block b, i.e. transpose of blocks, rows scrambled
        k = n // s
        def f(r, c):
            return (c, r)
        return {p: f(*p) for p in cells}
    raise ValueError(kind)


def run(k, s, kind, m=1, seed=0, policy="look", verbose=False, stop_at=0):
    rng = random.Random(seed)
    n = k * s
    perm = make_perm(n, s, kind, rng)
    sq = {(a, b): Counter() for a in range(k) for b in range(k)}
    X = None
    for (r, c), (tr, tc) in perm.items():
        g = (tr // s, tc // s)
        if (tr, tc) == (n - 1, n - 1):
            X = (r // s, c // s); continue
        sq[(r // s, c // s)][g] += 1

    def take(g, cnt, avoid_col=None, near_band=None):
        """remove cnt tiles of class g from reservoirs (Preparation), prefer
        tiles that would otherwise need a hop1 (outside column g[1])."""
        order = sorted(sq, key=lambda Y: (Y[1] == g[1], Y == g,
                                           abs(Y[0] - near_band) if near_band is not None else 0))
        got = 0
        for Y in order:
            t = min(cnt - got, sq[Y][g] - (1 if Y == g else 0))
            if t > 0:
                sq[Y][g] -= t; got += t
            if got == cnt: break
        return got

    # rows: R[(b,J)] = (left, right) arrays of target bands; index 0 next to block J
    R = {}
    for b in range(k):
        for J in range(k):
            sides = []
            for L in (J * s, (k - 1 - J) * s):
                arr = np.array([(i + b) % k for i in range(L)], dtype=np.int32)
                for band, cnt in Counter(arr.tolist()).items():
                    got = take((band, J), cnt, near_band=b)
                    if got < cnt:  # not enough tiles of that class: refill with others
                        pass
                sides.append(arr)
            R[(b, J)] = sides
    # seeds
    for b in range(k):
        for c in range(k):
            for a in range(k):
                if a == b: continue
                g = (a, c)
                got = take(g, m)
                sq[(b, c)][g] += got

    # column counts for hop1 availability: colcnt[Y][J] = tiles in Y with target col J, J != Y[1]
    def hop1_sources(X):
        b, J = X
        out = []
        for Jp in range(k):
            if Jp == J: continue
            Y = (b, Jp)
            if any(v for g, v in sq[Y].items() if g[1] == J):
                out.append(Y)
        return out

    def hop2_sources(X):
        a, c = X
        return [(bp, c) for bp in range(k) if bp != a and sq[(bp, c)][X] > 0]

    def legal(X):
        return [("V", Y) for Y in hop2_sources(X)] + [("H", Y) for Y in hop1_sources(X)]

    def misplaced():
        return sum(v for Y, C in sq.items() for g, v in C.items() if g != Y)

    transfers = {"H": 0, "V": 0}; relocs = 0; steps = 0
    wrong = misplaced()
    while True:
        steps += 1
        if steps > 20 * n * n:
            return None
        cands = legal(X)
        if not cands:
            mp = misplaced()
            if mp == 0 or mp <= stop_at: break
            # relocation: bring a class-X tile from anywhere (not rows), else any misplaced tile
            src = [(Y, X) for Y in sq if Y != X and sq[Y][X] > 0]
            if not src:
                src = [(Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y and Y != X]
            if not src:
                break
            Y, g = src[0]
            sq[Y][g] -= 1; sq[X][g] += 1; X = Y; relocs += 1
            continue
        # choose
        best = None
        for typ, Y in cands:
            if typ == "V":
                sq[Y][X] -= 1; sq[X][X] += 1
                nxt = len(legal(Y)) > 0
                sq[Y][X] += 1; sq[X][X] -= 1
                sc = (nxt, 1, sq[Y][X])
            else:
                nxt = True  # approximate: Y usually has work
                # does Y have anything to receive?  cheap check
                nxt = len(legal(Y)) > 0
                sc = (nxt, 0, 0)
            if policy == "random":
                sc = (nxt, rng.random())
            if best is None or sc > best[0]:
                best = (sc, typ, Y)
        _, typ, Y = best
        if typ == "V":
            sq[Y][X] -= 1; sq[X][X] += 1
        else:
            b, J = X
            Jp = Y[1]
            # choose T: tile in Y with target column J; prefer the band most demanded? take max count
            opts = [(v, g) for g, v in sq[Y].items() if v and g[1] == J]
            v, gT = max(opts)
            sq[Y][gT] -= 1
            side = 0 if Jp < J else 1
            arr = R[(b, J)][side]
            dist = (J - 1 - Jp) if Jp < J else (Jp - J - 1)
            p = dist * s + rng.randrange(s)
            F = int(arr[0])
            arr[0:p] = arr[1:p + 1].copy()
            arr[p] = gT[0]
            sq[X][(F, J)] += 1
        transfers[typ] += 1
        X = Y
    return transfers, relocs, n, misplaced()


if __name__ == "__main__":
    kinds = sys.argv[1].split(",") if len(sys.argv) > 1 else ["random", "transpose", "rot90", "rot180", "quadswap", "blockperm", "diagshift"]
    ks = [(4, 16), (5, 25), (6, 36)]
    for kind in kinds:
        for k, s in ks:
            for m in [0, 1, s // 2]:
                r = run(k, s, kind, m, stop_at=k * k * k * s)
                if r is None:
                    print(kind, k, s, m, "no termination", flush=True); continue
                t, rl, n, left = r
                print(f"{kind:9s} k={k:2d} s={s:2d} n={n:4d} m={m:2d} H/n2={t['H']/n**2:.3f} V/n2={t['V']/n**2:.3f} "
                      f"relocs={rl:6d} relocs*k/n2={rl*k/n**2:.3f} left/(k^2 n)={left/(k*k*n):.3f}", flush=True)
