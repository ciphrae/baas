"""Square-level count run with *axis-separable* transfers (rook moves).

Model (conceptual; corridor pools ignored, i.e. the transferred tile itself is
assumed to arrive): k x k squares, each holding a multiset of tile groups
(a,b) = target square.  One blank, in square X=(a,b).  A transfer into X takes
one tile T out of a square Y and puts it in X; the blank moves to Y.
  mode "rook":   H: Y=(a,b'') and col(T)=b ; V: Y=(a'',b) and band(T)=a
  mode "zhong":  Y anywhere and group(T)=X          (Algorithm 4)
If no transfer is available but the board is unsorted the run is STUCK and we
pay a 'relocation': one direct long-distance move of a tile (cost O(n)).
"""
import random
from collections import Counter

def make_board(k, s, kind, rng):
    n = k * s
    cells = [(r, c) for r in range(n) for c in range(n)]
    if kind == "random":
        tgt = cells[:]; rng.shuffle(tgt); perm = dict(zip(cells, tgt))
    elif kind == "transpose":
        perm = {(r, c): (c, r) for (r, c) in cells}
    elif kind == "rot90":
        perm = {(r, c): (c, n - 1 - r) for (r, c) in cells}
    elif kind == "rot180":
        perm = {(r, c): (n - 1 - r, n - 1 - c) for (r, c) in cells}
    elif kind == "diagshift":
        perm = {(r, c): ((r + s) % n, (c + s) % n) for (r, c) in cells}
    sq = {(a, b): Counter() for a in range(k) for b in range(k)}
    X = None
    for (r, c), (tr, tc) in perm.items():
        if (tr, tc) == (n - 1, n - 1):
            X = (r // s, c // s); continue
        sq[(r // s, c // s)][(tr // s, tc // s)] += 1
    return sq, X, n

def run(k, s, kind, mode="rook", seed=0):
    rng = random.Random(seed)
    sq, X, n = make_board(k, s, kind, rng)
    phi = lambda: sum(v * ((g[0] != Y[0]) + (g[1] != Y[1])) for Y, C in sq.items() for g, v in C.items())
    phi0 = phi()
    transfers = relocs = 0
    while True:
        a, b = X
        best = None
        for Y, C in sq.items():
            if Y == X:
                continue
            for g, v in C.items():
                if not v:
                    continue
                ok = (g == X) if mode == "zhong" else ((Y[0] == a and g[1] == b) or (Y[1] == b and g[0] == a))
                if not ok:
                    continue
                # prefer: tile fully home; then leaving the blank where work remains
                work = sum(vv for gg, vv in C.items() if gg != Y) - (1 if g != Y else 0)
                sc = (g == X, work > 0)
                if best is None or sc > best[0]:
                    best = (sc, Y, g)
        if best is None:
            wrong = [(Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y]
            if not wrong:
                break
            src = next(((Y, g) for Y, g in wrong if g == X), wrong[0])
            Y, g = src
            sq[Y][g] -= 1; sq[X][g] += 1; X = Y; relocs += 1
            continue
        _, Y, g = best
        sq[Y][g] -= 1; sq[X][g] += 1; X = Y; transfers += 1
    return transfers, relocs, phi0, n * n

if __name__ == "__main__":
    import sys
    for kind in ["random", "transpose", "rot90", "rot180", "diagshift"]:
        for k, s in [(4, 6), (6, 8), (8, 8)]:
            for mode in ["zhong", "rook"]:
                t, rl, p0, n2 = run(k, s, kind, mode)
                print(f"{kind:9s} {mode:5s} k={k} s={s} n={k*s:3d} transfers/n^2={t/n2:.3f} phi0/n^2={p0/n2:.3f} relocs={rl}", flush=True)
