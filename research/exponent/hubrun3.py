"""Two-hop transport with hub reservoirs as buffers: count model with exact rows,
better policy (pairing + look-ahead), explicit relocation accounting.

See hubrun.py for the model.  Changes:
- after a hop2 that withdraws class g from hub X, the replenishing hop1 into X
  inserts a tile T of the same class g when band(X) has one ("pairing"): then the
  pool (row R + stock of the hub) keeps its class multiset;
- hop2 prefers hubs from whose band the pairing can be done, then larger stock;
- every choice checks that the blank's next square has a legal move;
- relocation (stuck): carry one class-X tile directly into X (cost ~n); if X
  misses nothing, move one misplaced tile of some square Z into X (cost ~n).
Stops when at most stop_at reservoir tiles are misplaced (the rest is cleaned
up at O(n) each).
"""
import random, sys
import numpy as np
from collections import Counter
from hubrun import make_perm


def run(k, s, kind, m=1, seed=0, stop_at=None, fill="demand"):
    rng = random.Random(seed)
    n = k * s
    if stop_at is None:
        stop_at = k * k * n
    perm = make_perm(n, s, kind, rng)
    sq = {(a, b): Counter() for a in range(k) for b in range(k)}
    X = None
    for (r, c), (tr, tc) in perm.items():
        g = (tr // s, tc // s)
        if (tr, tc) == (n - 1, n - 1):
            X = (r // s, c // s); continue
        sq[(r // s, c // s)][g] += 1

    def take(g, cnt, near_band=None):
        order = sorted(sq, key=lambda Y: (Y[1] == g[1], Y == g,
                                           abs(Y[0] - near_band) if near_band is not None else 0))
        got = 0
        for Y in order:
            t = min(cnt - got, sq[Y][g] - (1 if Y == g else 0))
            if t > 0:
                sq[Y][g] -= t; got += t
            if got == cnt: break
        return got

    R = {}
    for b in range(k):
        for J in range(k):
            sides = []
            for L in (J * s, (k - 1 - J) * s):
                if fill == "cyclic":
                    arr = np.array([(i + b) % k for i in range(L)], dtype=np.int32)
                elif fill == "demand":
                    w = Counter()
                    for Jp in range(k):
                        if Jp == J: continue
                        for g, v in sq[(b, Jp)].items():
                            if g[1] == J: w[g[0]] += v
                    tot = sum(w.values())
                    if tot == 0:
                        arr = np.array([(i + b) % k for i in range(L)], dtype=np.int32)
                    else:
                        bands = [a for a in range(k) for _ in range(round(L * w[a] / tot))]
                        bands = (bands + [(i + b) % k for i in range(L)])[:L]
                        rng.shuffle(bands)
                        arr = np.array(bands, dtype=np.int32)
                else:
                    arr = np.array([rng.randrange(k) for i in range(L)], dtype=np.int32)
                for band, cnt in Counter(arr.tolist()).items():
                    take((band, J), cnt, near_band=b)
                sides.append(arr)
            R[(b, J)] = sides
    for b in range(k):
        for c in range(k):
            for a in range(k):
                if a != b:
                    sq[(b, c)][(a, c)] += take((a, c), m)

    def h1(X, cls=None):
        """hop1 sources into X: squares Y in band b, other column, with a tile of
        target column J (of class cls if given)."""
        b, J = X
        out = []
        for Jp in range(k):
            if Jp == J: continue
            Y = (b, Jp)
            if cls is None:
                if any(v for g, v in sq[Y].items() if g[1] == J): out.append(Y)
            elif sq[Y][cls] > 0:
                out.append(Y)
        return out

    def h2(X):
        a, c = X
        return [(bp, c) for bp in range(k) if bp != a and sq[(bp, c)][X] > 0]

    def has_move(X):
        return bool(h2(X)) or bool(h1(X))

    def misplaced():
        return sum(v for Y, C in sq.items() for g, v in C.items() if g != Y)

    cnt = Counter(); relocs = Counter()
    last_withdrawn = None
    guard = 0
    mp = misplaced()
    while True:
        guard += 1
        if guard > 30 * n * n:
            return None
        b, J = X
        move = None
        # 1. pairing hop1
        if last_withdrawn is not None:
            srcs = h1(X, last_withdrawn)
            good = [Y for Y in srcs if has_move(Y)]
            if good or srcs:
                Y = (good or srcs)[0]
                move = ("H", Y, last_withdrawn)
        if move is None:
            # 2. hop2 into X
            hubs = h2(X)
            if hubs:
                def score(Y):
                    sq[Y][X] -= 1; sq[X][X] += 1
                    ok = has_move(Y)
                    sq[Y][X] += 1; sq[X][X] -= 1
                    pair = bool(h1(Y, X))
                    return (ok, pair, sq[Y][X])
                Y = max(hubs, key=score)
                move = ("V", Y, X)
        if move is None:
            srcs = h1(X)
            if srcs:
                def score(Y):
                    return (has_move(Y), sum(v for g, v in sq[Y].items() if g[1] == J))
                Y = max(srcs, key=score)
                opts = [(v, g) for g, v in sq[Y].items() if v and g[1] == J]
                # T: prefer class whose column-J hubs have least stock (feed demand)
                def need(g):
                    return -sum(sq[(bb, J)][g] for bb in range(k) if (bb, J) != g)
                g = max(opts, key=lambda vg: (need(vg[1]), vg[0]))[1]
                move = ("H", Y, g)
        if move is None:
            if mp <= stop_at:
                break
            src = [Y for Y in sq if Y != X and sq[Y][X] > 0]
            if src:
                Y = max(src, key=has_move)
                sq[Y][X] -= 1; sq[X][X] += 1; X = Y; relocs["own"] += 1
                last_withdrawn = None; mp -= 1
                continue
            cands = [(Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y and Y != X]
            if not cands:
                break
            Y, g = cands[rng.randrange(len(cands))]
            sq[Y][g] -= 1; sq[X][g] += 1; X = Y; relocs["foreign"] += 1
            last_withdrawn = None
            continue
        typ, Y, g = move
        if typ == "V":
            sq[Y][g] -= 1; sq[X][g] += 1; mp -= 1
            last_withdrawn = g
        else:
            sq[Y][g] -= 1; mp -= 1
            Jp = Y[1]
            side = 0 if Jp < J else 1
            arr = R[(b, J)][side]
            dist = (J - 1 - Jp) if Jp < J else (Jp - J - 1)
            p = dist * s + rng.randrange(s)
            F = int(arr[0])
            arr[0:p] = arr[1:p + 1].copy()
            arr[p] = g[0]
            sq[X][(F, J)] += 1
            if (F, J) != X: mp += 1
            last_withdrawn = None
        cnt[typ] += 1
        X = Y
    return cnt, relocs, n, misplaced()


if __name__ == "__main__":
    kinds = sys.argv[1].split(",")
    ks = [tuple(map(int, x.split("x"))) for x in sys.argv[2].split(",")]
    ms = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [1]
    for kind in kinds:
        for k, s in ks:
            for m in ms:
                r = run(k, s, kind, m)
                if r is None:
                    print(kind, k, s, m, "no termination", flush=True); continue
                c, rl, n, left = r
                tot = rl["own"] + rl["foreign"]
                print(f"{kind:9s} k={k:2d} s={s:3d} n={n:4d} m={m:2d} H/n2={c['H']/n**2:.3f} V/n2={c['V']/n**2:.3f} "
                      f"relocs own={rl['own']} foreign={rl['foreign']} relocs*k/n2={tot*k/n**2:.4f} "
                      f"left/(k^2 n)={left/(k*k*n):.2f}", flush=True)
