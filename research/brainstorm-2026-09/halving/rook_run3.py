"""Rook count run where each STUCK relocation is chosen by rollout: try every
relocation type (move one tile of group g from square Y into the blank's square
by a direct long carry), run the greedy policy until the next stuck, keep the
best.  Reports #transfers and #relocations (each relocation costs O(n))."""
import random, copy
from collections import Counter
from rook_run import make_board
from rook_run2 import legal

def greedy_step(sq, X, k):
    cands = legal(sq, X, k)
    if not cands: return None
    best = None
    for Y, g in cands:
        sq[Y][g] -= 1; sq[X][g] += 1
        nxt = legal(sq, Y, k)
        sc = (len(nxt) > 0, g == X)
        sq[Y][g] += 1; sq[X][g] -= 1
        if best is None or sc > best[0]: best = (sc, Y, g)
    return best[1], best[2]

def rollout(sq, X, k, cap):
    sq = copy.deepcopy(sq); steps = 0
    while steps < cap:
        mv = greedy_step(sq, X, k)
        if mv is None: break
        Y, g = mv; sq[Y][g] -= 1; sq[X][g] += 1; X = Y; steps += 1
    wrong = sum(v for Y, C in sq.items() for g, v in C.items() if g != Y)
    return steps, wrong

def run(k, s, kind, seed=0, cap=400):
    rng = random.Random(seed)
    sq, X, n = make_board(k, s, kind, rng)
    transfers = relocs = 0
    while True:
        mv = greedy_step(sq, X, k)
        if mv is None:
            wrong = sorted({(Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y})
            if not wrong: break
            best = None
            for Y, g in wrong:
                sq[Y][g] -= 1; sq[X][g] += 1
                st, w = rollout(sq, Y, k, cap)
                sq[Y][g] += 1; sq[X][g] -= 1
                sc = (st if w else 10**9, -w)
                if best is None or sc > best[0]: best = (sc, Y, g)
            _, Y, g = best
            sq[Y][g] -= 1; sq[X][g] += 1; X = Y; relocs += 1; continue
        Y, g = mv; sq[Y][g] -= 1; sq[X][g] += 1; X = Y; transfers += 1
    return transfers, relocs, n * n

if __name__ == "__main__":
    import sys
    for kind in ["transpose", "rot90", "random", "diagshift", "rot180"]:
        for k, s in [(4, 6), (6, 6), (8, 6)]:
            t, rl, n2 = run(k, s, kind)
            print(f"{kind:9s} k={k} s={s} n={k*s:3d} transfers/n^2={t/n2:.3f} relocs={rl} (k^2={k*k})", flush=True)
