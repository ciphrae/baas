"""Two-hop transport in Euler rounds (count model).

T[S, D] = tiles at square S whose target square is D (home tiles are loops).
T is s^2-regular, so it splits into s^2 perfect matchings pi_r (Koenig).  In
round r every square S with pi_r(S) != S sends one tile, of class pi_r(S), and
receives one tile of its own class.

Blank walk.  The blank at D = (a, c) takes a class-D tile from the stock of a
hub h = (b, c) (hop2 down column c), then refills h by a hop1 from a band-b
source S whose round tile goes to column c (it enters row R(b, c); the row's
head drops into h).  The blank is now at S.  So square S is an edge
col(pi(S)) -> col(S) of a multigraph G_r on the k columns; in = out = k at every
vertex, and a round is an Euler circuit of G_r.  At vertex c the walk pairs each
arrival D (a column-c square) with a departure S (col pi(S) = c); the hub is
(band S, c).  Departures in the same band are interchangeable, so all closed
trails meeting at one (vertex, band) group merge for free.
    cycles per round = relocations per round (O(n) each)

Stock.  Row R(b, c) outputs are exogenous (they depend on pi only).  Per round
and column: max-weight assignment of arrival classes to departures, feasible
if the hub (band of the departure) has stock >= 1, weight = stock (D = hub
itself needs no stock).  No such band: a vertical O(n)
carry from the column's richest hub (counted in 'carry'); no stock anywhere in
the column: 'hard'.

Rows start in steady state: the first W rounds are run on the rows only.
Seeds: m tiles of every class in every hub (virtual).
"""
import sys, random
import numpy as np
from scipy.optimize import linear_sum_assignment
from hubrun import make_perm
CARRY_LOG = []


def traffic_matrix(k, s, kind, seed):
    rng = random.Random(seed)
    n = k * s
    perm = make_perm(n, s, kind, rng)
    K = k * k
    T = np.zeros((K, K), dtype=np.int64)
    for (r, c), (tr, tc) in perm.items():
        T[(r // s) * k + c // s, (tr // s) * k + tc // s] += 1
    return T


def rounds(T, rng):
    """s^2 perfect matchings in the support of T (T regular bipartite)"""
    T = T.copy()
    K = len(T)
    R = int(T[0].sum())
    for _ in range(R):
        w = np.where(T > 0, 1e6 + T + rng.random((K, K)), 0.0)
        rows, cols = linear_sum_assignment(-w)
        assert (T[rows, cols] > 0).all()
        T[rows, cols] -= 1
        yield cols.copy()


class Rows:
    def __init__(self, k, s, rng):
        self.k, self.s, self.rng = k, s, rng
        self.arr = {}
        for b in range(k):
            for c in range(k):
                for side in (0, 1):
                    L = c * s if side == 0 else (k - 1 - c) * s
                    self.arr[(b, c, side)] = np.array([rng.randrange(k) for _ in range(L)], dtype=np.int32)

    def hop(self, S, D):
        """S sends its tile (class D) into row R(band S, col D); returns the head (band of its class)"""
        k, s = self.k, self.s
        b, J = divmod(S, k)
        a, c = divmod(D, k)
        side = 0 if J < c else 1
        arr = self.arr[(b, c, side)]
        dist = (c - 1 - J) if J < c else (J - c - 1)
        p = min(dist * s + self.rng.randrange(s), len(arr) - 1)
        F = int(arr[0])
        arr[0:p] = arr[1:p + 1]
        arr[p] = a
        return F


def run(k, s, kind, m=4, seed=0, warm=None, merge=True):
    rng = random.Random(seed)
    nprng = np.random.default_rng(seed)
    n = k * s
    K = k * k
    T = traffic_matrix(k, s, kind, seed)
    rows = Rows(k, s, rng)
    # warm-up on the rows only
    W = 2 * n if warm is None else warm
    Tw = T.copy()
    for r, pi in enumerate(rounds(Tw, nprng)):
        if r >= W: break
        for S in range(K):
            if pi[S] != S and pi[S] % k != S % k:
                rows.hop(S, pi[S])
    # stock[b, c, a]: class (a, c) tiles in hub (b, c)
    stock = np.full((k, k, k), m, dtype=np.int64)
    st = dict(cycles=0, comps=0, carry=0, hard=0, rounds=0, minstock=m)
    for pi in rounds(T, nprng):
        st["rounds"] += 1
        movers = [S for S in range(K) if pi[S] != S]
        # arrivals at vertex c: movers in column c; departures: movers with col pi(S) = c.
        # Same-column movers (col pi(S) = col S) use hop2 only (their tile goes
        # straight down C(c, .)); in G_r they are loops at c and still pair up.
        trans = {}          # D -> departure S
        group = {}          # D -> (c, band of S)
        for c in range(k):
            arr_c = [D for D in movers if D % k == c]
            dep_c = [S for S in movers if pi[S] % k == c]
            assert len(arr_c) == len(dep_c)
            byband = {}
            for S in dep_c:
                byband.setdefault(S // k, []).append(S)
            cap = {b: len(v) for b, v in byband.items()}
            # max-weight assignment of arrival classes to departure slots (MaxWeight):
            # own hub free, else stock >= 1 weighted by stock; infeasible pairs cost a carry
            slots = [S for S in dep_c]
            Wt = np.empty((len(arr_c), len(slots)))
            for i, D in enumerate(arr_c):
                a = D // k
                for j, S in enumerate(slots):
                    bb = S // k
                    # lexicographic: feasible pairs, then own-hub pairs, then stock
                    if bb == a: Wt[i, j] = 1e9 + 1e6
                    elif stock[bb, c, a] >= 1: Wt[i, j] = 1e9 + min(stock[bb, c, a], 1e5)
                    else: Wt[i, j] = max(stock[bb, c, a], -1e5)
            ri, cj = linear_sum_assignment(-Wt)
            for i, j in zip(ri, cj):
                D = arr_c[i]; S = slots[j]; a = D // k; bb = S // k
                if bb != a:
                    if stock[bb, c, a] >= 1:
                        stock[bb, c, a] -= 1
                    else:
                        rich = int(np.argmax(stock[:, c, a]))
                        if stock[rich, c, a] <= 0: st["hard"] += 1
                        else:
                            st["carry"] += 1
                            CARRY_LOG.append((st["rounds"], c, a, bb))
                        stock[rich, c, a] -= 1
                trans[D] = S
                group[D] = (c, bb)
        # hop1s: each mover S inserts into row R(band S, col pi(S)) unless same column
        for S in movers:
            D = pi[S]
            if D % k != S % k:
                F = rows.hop(S, D)
                stock[S // k, D % k, F] += 1
            else:
                # same-column tile goes by hop2 directly: it is its own stock
                stock[S // k, D % k, D // k] += 1
        st["minstock"] = min(st["minstock"], int(stock.min()))
        # cycles of the transition system D -> trans[D] (next arrival is trans[D])
        seen = {}
        cyc = 0
        for D0 in trans:
            if D0 in seen: continue
            D = D0
            while D not in seen:
                seen[D] = cyc
                D = trans[D]
            cyc += 1
        # union cycles sharing a (vertex, band) group
        parent = list(range(cyc))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]; x = parent[x]
            return x
        first = {}
        for D, gkey in group.items():
            cid = find(seen[D])
            if gkey in first:
                parent[find(first[gkey])] = cid
            else:
                first[gkey] = cid
        merged = len({find(x) for x in range(cyc)}) if merge else cyc
        st["cycles"] += merged
        # components of G_r (lower bound)
        par = list(range(k))
        def f2(x):
            while par[x] != x:
                par[x] = par[par[x]]; x = par[x]
            return x
        used = set()
        for S in movers:
            u, v = pi[S] % k, S % k
            used.add(u); used.add(v)
            par[f2(u)] = f2(v)
        st["comps"] += len({f2(x) for x in used})
    return st, n


if __name__ == "__main__":
    kinds = sys.argv[1].split(",")
    ks = [tuple(map(int, x.split("x"))) for x in sys.argv[2].split(",")]
    ms = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [4]
    for kind in kinds:
        for k, s in ks:
            for m in ms:
                st, n = run(k, s, kind, m)
                R = st["rounds"]
                print(f"{kind:9s} k={k:2d} s={s:3d} m={m:3d} cycles/round={st['cycles']/R:.3f} "
                      f"comps/round={st['comps']/R:.3f} carry={st['carry']} hard={st['hard']} "
                      f"(cycles+carry)*k/n2={(st['cycles']+st['carry']+st['hard'])*k/n**2:.4f} minstock={st['minstock']}",
                      flush=True)
