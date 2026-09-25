"""Count model for 'axis-separable corridors with queues' (k^2 n corridor tiles).
Corridors: R(a',c) = row in band a' holding tiles whose target column block is c
(any band) -> modelled as a fully mixed pool P[(a',c)] (OPTIMISTIC: ignores FIFO
position inside the row).  C(c,a) = column in strip c holding group (a,c) only
(pass-through, its content is invariant).
Blank alternates:
 at reservoir X=(a,c): V-step: dequeue a group-X tile from some pool P[(a',c)]
      into C(c,a); C delivers a group-X tile into X; blank -> junction (a',c).
 at junction (a',c): H-step: enqueue into P[(a',c)] a col-c tile T taken from a
      reservoir (a',b') of band a' (T not home); blank -> reservoir (a',b').
Stuck -> relocation (one O(n) long carry).  Pool stock q per pool, spread evenly
over target bands, taken from non-home tiles (Preparation)."""
import random
from collections import Counter
from rook_run import make_board

def run(k, s, kind, q, seed=0):
    rng = random.Random(seed)
    sq, X, n = make_board(k, s, kind, rng)
    P = {(a, c): Counter() for a in range(k) for c in range(k)}
    # stock pools: for pool (a',c) take q//k tiles of each group (x,c), prefer non-home, prefer from band a'
    for (ap, c) in P:
        for x in range(k):
            g = (x, c); need = q // k
            srcs = sorted((Y for Y in sq if sq[Y][g] > 0 and Y != g), key=lambda Y: abs(Y[0] - ap))
            srcs += [g] if sq[g][g] > 0 else []
            for Y in srcs:
                t = min(need, sq[Y][g] - (1 if Y == g else 0))
                if t > 0: sq[Y][g] -= t; P[(ap, c)][g] += t; need -= t
                if need == 0: break
    wrong = lambda: sum(v for Y, C in sq.items() for g, v in C.items() if g != Y)
    state = ("res", X); steps = relocs = bounces = 0; forbid = None
    guard = 0
    while True:
        guard += 1
        if guard > 50 * n * n: return None
        kindst, Z = state
        if kindst == "res":
            a, c = Z
            opts = [ap for ap in range(k) if P[(ap, c)][Z] > 0 and (ap, c) != forbid]; forbid = None
            if opts:
                # prefer junction whose band has work for pool (a',c)
                def work(ap):
                    return sum(v for b in range(k) for g, v in sq[(ap, b)].items() if g[1] == c and g != (ap, b))
                ap = max(opts, key=work)
                P[(ap, c)][Z] -= 1; sq[Z][Z] += 1; state = ("jun", (ap, c)); steps += 1; continue
            if wrong() == 0: break
            # relocation: long carry of a group-Z tile from some reservoir into Z
            src = next((Y for Y in sq if Y != Z and sq[Y][Z] > 0), None)
            if src is None:  # take any wrong tile anywhere into... move blank to a reservoir with a wrong tile
                src, g = next((Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y)
            else:
                g = Z
            sq[src][g] -= 1; sq[Z][g] += 1; state = ("res", src); relocs += 1; continue
        else:
            ap, c = Z
            cands = [(b, g) for b in range(k) for g, v in sq[(ap, b)].items() if v and g[1] == c and g != (ap, b)]
            if cands:
                # prefer taking from a reservoir that then can receive a tile from pools
                def ok(bg):
                    b, g = bg; Y = (ap, b)
                    return any(P[(x, b)][Y] > 0 for x in range(k))
                cands.sort(key=lambda bg: (not ok(bg),))
                b, g = cands[0]
                sq[(ap, b)][g] -= 1; P[Z][g] += 1; state = ("res", (ap, b)); steps += 1; continue
            # no col-c work in band a': 'bounce' = enqueue a HOME tile of (a',c) (still a
            # col-c tile, so the queue stays valid; cost O(s)), blank -> reservoir (a',c);
            # its next V-step must use another pool (forbid returning to the same one).
            if wrong() == 0: break
            Y = (ap, c)
            strip_work = any(g[1] == c and g != W for W, C in sq.items() for g, v in C.items() if v)
            if strip_work and sq[Y][Y] > 0:
                sq[Y][Y] -= 1; P[Z][Y] += 1; state = ("res", Y); bounces += 1; forbid = Z; continue
            # strip c exhausted: one long carry takes a wrong tile g from reservoir Y
            # directly to its home (a home tile of that home goes to pool P[Z]? no:
            # we model it as a direct transfer g: Y -> home(g), blank -> Y).
            Y, g = next((Y, g) for Y, C in sq.items() for g, v in C.items() if v and g != Y)
            # blank is in the corridor at Z; conceptually: pool P[Z] keeps size by
            # taking a home tile of (ap,c) is impossible here; so just move g home and
            # the displaced home tile of home(g) into P[Z] (a col-c tile iff home(g)[1]==c)
            sq[Y][g] -= 1; P[Z][g] += 1
            state = ("res", Y); relocs += 1; continue
    return steps, relocs, bounces, n * n

if __name__ == "__main__":
    for kind in ["transpose", "rot90", "rot180", "diagshift", "random"]:
        for k, s in [(4, 8), (6, 8), (8, 8)]:
            for q in [s, 4 * s]:
                r = run(k, s, kind, q)
                if r is None: print(kind, k, s, q, "no termination"); continue
                st, rl, bo, n2 = r
                print(f"{kind:9s} k={k} s={s} n={k*s:3d} q={q:3d} steps/n^2={st/n2:.3f} bounces/n^2={bo/n2:.3f} relocs={rl}", flush=True)
