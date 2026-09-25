"""Idealized recursive halving (lower-bound model).
Region = rectangle; split along the longer side.  Tiles whose target lies in
the other half swap places with tiles of the other class (counts are equal
because the region holds exactly its own tiles).  Each moved tile goes from
cell p to cell q; charge ineff = (d(p,q)+d(q,t)-d(p,t))/2 (Manhattan detour),
i.e. we assume a perfect transport that wastes NOTHING except the fact that
q is not t.  Real loop/carry implementations cost more.
assignment: 'oblivious' = random matching of vacated cells,
            'stable'    = order-preserving (as a stable partition/conveyor does),
            'optimal'   = min-cost matching (target-aware landing)."""
import numpy as np, sys
from scipy.optimize import linear_sum_assignment
rng = np.random.default_rng(0)

def board(n, kind):
    P = np.array([(r, c) for r in range(n) for c in range(n)])
    if kind == "random": T = P[rng.permutation(n * n)]
    elif kind == "transpose": T = P[:, ::-1]
    elif kind == "rot90": T = np.stack([P[:, 1], n - 1 - P[:, 0]], 1)
    elif kind == "rot180": T = n - 1 - P
    return P.copy(), T

def solve(n, kind, mode):
    pos, tgt = board(n, kind)
    total = 0.0
    regions = [(0, n, 0, n, np.arange(n * n))]
    while regions:
        r0, r1, c0, c1, idx = regions.pop()
        h, w = r1 - r0, c1 - c0
        if h * w <= 1: continue
        ax = 0 if h >= w else 1
        lo, hi = (r0, r1) if ax == 0 else (c0, c1)
        mid = (lo + hi) // 2
        up_t = tgt[idx, ax] < mid; up_p = pos[idx, ax] < mid
        A = idx[up_t & ~up_p]; B = idx[~up_t & up_p]   # A must go to first half, B second
        assert len(A) == len(B)
        if len(A):
            pa, pb = pos[A].copy(), pos[B].copy()
            for movers, dst in ((A, pb), (B, pa)):
                src = pos[movers] if movers is A else pb
                src = pa if movers is A else pb
                t = tgt[movers]
                if mode == "oblivious":
                    perm = rng.permutation(len(dst))
                elif mode == "stable":
                    o1 = np.lexsort((src[:, 1 - ax], src[:, ax])); o2 = np.lexsort((dst[:, 1 - ax], dst[:, ax]))
                    perm = np.empty(len(dst), int); perm[o1] = o2
                else:
                    C = (np.abs(src[:, None, :] - dst[None, :, :]).sum(2) + np.abs(dst[None, :, :] - t[:, None, :]).sum(2))
                    _, perm = linear_sum_assignment(C)
                q = dst[perm]
                d = lambda x, y: np.abs(x - y).sum(1)
                total += ((d(src, q) + d(q, t) - d(src, t)) / 2).sum()
                pos[movers] = q
        if ax == 0:
            halves = [(r0, mid, c0, c1), (mid, r1, c0, c1)]
        else:
            halves = [(r0, r1, c0, mid), (r0, r1, mid, c1)]
        for (a0, a1, b0, b1) in halves:
            m = (tgt[idx, 0] >= a0) & (tgt[idx, 0] < a1) & (tgt[idx, 1] >= b0) & (tgt[idx, 1] < b1)
            regions.append((a0, a1, b0, b1, idx[m]))
    return total

if __name__ == "__main__":
    for kind in ["random", "rot180", "rot90", "transpose"]:
        for mode in ["oblivious", "stable", "optimal"]:
            row = []
            for n in ([16, 32, 64] if mode != "optimal" else [16, 32]):
                row.append(f"n={n}: {solve(n, kind, mode)/n**3:.4f}")
            print(f"{kind:9s} {mode:9s} ineff/n^3  " + "  ".join(row), flush=True)
