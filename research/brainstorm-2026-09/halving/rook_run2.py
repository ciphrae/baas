"""Rook count run with one-step look-ahead: prefer transfers after which the
blank (at the source Y) still has a legal transfer.  Same model as rook_run.py."""
import random
from collections import Counter
from rook_run import make_board

def legal(sq, X, k):
    a, b = X
    out = []
    for Y, C in sq.items():
        if Y == X: continue
        if Y[0] != a and Y[1] != b: continue
        for g, v in C.items():
            if v and ((Y[0] == a and g[1] == b) or (Y[1] == b and g[0] == a)):
                out.append((Y, g))
    return out

def run(k, s, kind, seed=0):
    rng = random.Random(seed)
    sq, X, n = make_board(k, s, kind, rng)
    transfers = relocs = 0
    while True:
        cands = legal(sq, X, k)
        if not cands:
            wrong = [(Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y]
            if not wrong: break
            # relocation: prefer a group-X tile, else one whose removal leaves the blank
            # where a legal move exists
            best = None
            for Y, g in wrong:
                sq[Y][g] -= 1; sq[X][g] += 1
                sc = (g == X, len(legal(sq, Y, k)) > 0)
                sq[Y][g] += 1; sq[X][g] -= 1
                if best is None or sc > best[0]: best = (sc, Y, g)
            _, Y, g = best
            sq[Y][g] -= 1; sq[X][g] += 1; X = Y; relocs += 1; continue
        best = None
        for Y, g in cands:
            sq[Y][g] -= 1; sq[X][g] += 1
            nxt = legal(sq, Y, k)
            wrongY = any(v and gg != Y for gg, v in sq[Y].items())
            sc = (len(nxt) > 0, g == X, sum(1 for Z, h in nxt if h == Z) > 0 or False)
            sq[Y][g] += 1; sq[X][g] -= 1
            if best is None or sc > best[0]: best = (sc, Y, g)
        _, Y, g = best
        sq[Y][g] -= 1; sq[X][g] += 1; X = Y; transfers += 1
    return transfers, relocs, n * n

if __name__ == "__main__":
    for kind in ["random", "transpose", "rot90", "rot180", "diagshift"]:
        for k, s in [(4, 6), (6, 6), (8, 6)]:
            t, rl, n2 = run(k, s, kind)
            print(f"{kind:9s} k={k} s={s} n={k*s:3d} transfers/n^2={t/n2:.3f} relocs={rl} relocs/n^2={rl/n2:.3f}", flush=True)
