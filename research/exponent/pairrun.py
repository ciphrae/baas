"""Euler rounds with own-sender pairing (count model).

T splits into Delta perfect matchings pi_r (loops = home tiles); rounds run in random
order.  In round r the walk follows the cycles of pi_r: D is served from hub
(band of pi^-1(D), col D), then pi^-1(D) inserts its round tile -- class D -- into that
hub's row.  So every hub serves exactly the classes it inserts, and

    stock_b[x](t) = seeds_b[x] + prefill_b[x] - inflight_b[x](t)      (exactly).

Stock never runs out iff seeds_b[x] >= max_t inflight_b[x](t) - prefill_b[x] + 1.  This
script measures, per hub, need_b = sum_x max_t (inflight_b[x](t) - prefill_b[x])^+ (the
seeds that hub needs) against n, the length of a board row.  Same-column senders go
straight down their column (no row), same-band senders feed D directly (own class, no
stock needed); both are handled by skipping the row or the stock requirement.

Relocations: one per cycle of pi_r; started in snake order they cost O(k^2 s) per round
whatever their number, so only the cycle count is reported.
"""
import sys, random
import numpy as np
from eulerrun import traffic_matrix, rounds


def run(k, s, kind, seed=0, prefill="uniform", offset="rand"):
    rng = random.Random(seed)
    nprng = np.random.default_rng(seed)
    n = k * s
    K = k * k
    T = traffic_matrix(k, s, kind, seed)
    mats = list(rounds(T, nprng))
    rng.shuffle(mats)                        # random order of rounds
    # rows: (b, c, side) -> array of class bands (column c implicit)
    rows = {}
    for b in range(k):
        for c in range(k):
            for side in (0, 1):
                L = c * s if side == 0 else (k - 1 - c) * s
                if prefill == "uniform":
                    arr = [rng.randrange(k) for _ in range(L)]
                else:
                    arr = [0] * L
                rows[(b, c, side)] = np.array(arr, dtype=np.int32)
    # inflight[b, c, x] and prefill counts
    infl = np.zeros((k, k, k), dtype=np.int64)
    for (b, c, side), arr in rows.items():
        for x in arr:
            infl[b, c, x] += 1
    pre = infl.copy()
    peak = infl.copy()
    cycles = 0
    for pi in mats:
        seen = np.zeros(K, dtype=bool)
        for S0 in range(K):
            if seen[S0] or pi[S0] == S0:
                seen[S0] = True
                continue
            cycles += 1
            S = S0
            while not seen[S]:
                seen[S] = True
                D = int(pi[S])
                bS, J = divmod(S, k)
                a, c = divmod(D, k)
                if J != c:
                    side = 0 if J < c else 1
                    arr = rows[(bS, c, side)]
                    dist = (c - 1 - J) if J < c else (J - c - 1)
                    u = rng.randrange(s) if offset == "rand" else (s - 1 if offset == "far" else s // 2)
                    p = min(dist * s + u, len(arr) - 1)
                    F = int(arr[0])
                    arr[0:p] = arr[1:p + 1]
                    arr[p] = a
                    infl[bS, c, F] -= 1
                    infl[bS, c, a] += 1
                    if infl[bS, c, a] > peak[bS, c, a]:
                        peak[bS, c, a] = infl[bS, c, a]
                S = D
    need = np.maximum(peak - pre, 0)
    # own class (x = b) needs no stock: exclude
    for b in range(k):
        need[b, :, b] = 0
    per_hub = need.sum(axis=2)               # [b, c]
    return dict(n=n, rounds=len(mats), cycles=cycles, hub_max=int(per_hub.max()),
                hub_mean=float(per_hub.mean()), total=int(need.sum()),
                pair_max=int(need.max()))


if __name__ == "__main__":
    kinds = sys.argv[1].split(",")
    ks = [tuple(map(int, x.split("x"))) for x in sys.argv[2].split(",")]
    for kind in kinds:
        for k, s in ks:
            r = run(k, s, kind)
            n = r["n"]
            print(f"{kind:9s} k={k:2d} s={s:3d} n={n:4d} seeds/hub max={r['hub_max']/n:.3f}n "
                  f"mean={r['hub_mean']/n:.3f}n  max per (hub,class)={r['pair_max']}  "
                  f"total seeds/(k^2 n)={r['total']/(k*k*n):.3f}  cycles/round={r['cycles']/r['rounds']:.2f}",
                  flush=True)
