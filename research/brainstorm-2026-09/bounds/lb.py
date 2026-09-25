"""Lower bounds on OPT and on inefficiency I = (OPT - M)/2 for special n x n boards.

Board: dict cell (x, y) -> tile, tile 0 = blank.  Target: T(x, y) = n*x + y + 1 mod n^2,
blank at (n-1, n-1).  A symmetry g of the square gives the board B(g(c)) = T(c).
"""
import sys
from bisect import bisect_left


def target(n):
    return {(x, y): (n * x + y + 1) % (n * n) for x in range(n) for y in range(n)}


def goal_cell(n, t):
    if t == 0:
        return (n - 1, n - 1)
    return ((t - 1) // n, (t - 1) % n)


SYMS = {
    'rot180': lambda n, x, y: (n - 1 - x, n - 1 - y),
    'rot90': lambda n, x, y: (y, n - 1 - x),
    'transpose': lambda n, x, y: (y, x),
    'antitranspose': lambda n, x, y: (n - 1 - y, n - 1 - x),
    'mirror': lambda n, x, y: (x, n - 1 - y),        # each row reversed
    'flip': lambda n, x, y: (n - 1 - x, y),          # each column reversed
}


def sym_board(n, name):
    T = target(n)
    g = SYMS[name]
    return {g(n, x, y): T[(x, y)] for (x, y) in T}


def perm_parity(seq):
    seen = [False] * len(seq)
    par = 0
    for i in range(len(seq)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = seq[j]
                L += 1
            par ^= (L - 1) & 1
    return par


def reachable(n, B):
    # permutation of cells: cell c holds tile whose goal cell is g; parity + blank distance
    cells = [(x, y) for x in range(n) for y in range(n)]
    idx = {c: i for i, c in enumerate(cells)}
    seq = [idx[goal_cell(n, B[c])] for c in cells]
    b = next(c for c in cells if B[c] == 0)
    d = (n - 1 - b[0]) + (n - 1 - b[1])
    return perm_parity(seq) == d % 2


def fix_parity(n, B):
    """If unreachable, swap two tiles far from the blank in the middle of the board (cost O(1))."""
    if reachable(n, B):
        return B, False
    B = dict(B)
    # swap two horizontally adjacent tiles in row 0 not the blank
    cands = [((0, 0), (0, 1)), ((0, 1), (0, 2)), ((1, 0), (1, 1))]
    for a, c in cands:
        if B[a] != 0 and B[c] != 0:
            B[a], B[c] = B[c], B[a]
            break
    assert reachable(n, B)
    return B, True


def manhattan(n, B):
    V = H = 0
    for (x, y), t in B.items():
        if t:
            gx, gy = goal_cell(n, t)
            V += abs(x - gx)
            H += abs(y - gy)
    return V, H


def lis_len(a):
    tails = []
    for v in a:
        i = bisect_left(tails, v)
        if i == len(tails):
            tails.append(v)
        else:
            tails[i] = v
    return len(tails)


def linear_conflict(n, B):
    """Forced first departures: rows (vertical inefficient moves), cols (horizontal)."""
    R = C = 0
    for x in range(n):
        seq = [goal_cell(n, B[(x, y)])[1] for y in range(n) if B[(x, y)] and goal_cell(n, B[(x, y)])[0] == x]
        R += len(seq) - lis_len(seq)
    for y in range(n):
        seq = [goal_cell(n, B[(x, y)])[0] for x in range(n) if B[(x, y)] and goal_cell(n, B[(x, y)])[1] == y]
        C += len(seq) - lis_len(seq)
    return R, C


def inversions(a):
    # merge-sort count
    def rec(a):
        if len(a) <= 1:
            return a, 0
        m = len(a) // 2
        l, x = rec(a[:m])
        r, y = rec(a[m:])
        out, i, j, c = [], 0, 0, x + y
        while i < len(l) and j < len(r):
            if l[i] <= r[j]:
                out.append(l[i]); i += 1
            else:
                out.append(r[j]); j += 1; c += len(l) - i
        out += l[i:] + r[j:]
        return out, c
    return rec(list(a))[1]


def min_steps(inv, n):
    """Min number of moves, each changing inversions by an amount of parity (n-1)%2 and |.|<=n-1."""
    import math
    k = math.ceil(inv / (n - 1)) if inv else 0
    if (n - 1) % 2 == 1:  # each step odd => k ≡ inv mod 2
        if (k - inv) % 2:
            k += 1
    return k


def inversion_distance(n, B):
    rowkey = lambda t: goal_cell(n, t)[0] * n + goal_cell(n, t)[1]
    colkey = lambda t: goal_cell(n, t)[1] * n + goal_cell(n, t)[0]
    rs = [rowkey(B[(x, y)]) for x in range(n) for y in range(n) if B[(x, y)]]
    cs = [colkey(B[(x, y)]) for y in range(n) for x in range(n) if B[(x, y)]]
    return min_steps(inversions(rs), n), min_steps(inversions(cs), n)


def bounds(n, B):
    V, H = manhattan(n, B)
    LR, LC = linear_conflict(n, B)
    IV, IH = inversion_distance(n, B)
    vert = max(V + 2 * LR, IV)
    hor = max(H + 2 * LC, IH)
    M = V + H
    return dict(M=M, V=V, H=H, LCr=LR, LCc=LC, IDv=IV, IDh=IH, LB=vert + hor, Ilb=(vert + hor - M) / 2)


if __name__ == '__main__':
    ns = [int(a) for a in sys.argv[1:]] or [3, 4, 5, 6, 7, 8, 10, 16, 32, 64]
    for name in SYMS:
        print(name)
        for n in ns:
            B, fixed = fix_parity(n, sym_board(n, name))
            b = bounds(n, B)
            print(f"  n={n:3d} fix={int(fixed)} M={b['M']:7d} (n^3={n**3}) LCr={b['LCr']:5d} LCc={b['LCc']:5d} "
                  f"IDv-V={b['IDv']-b['V']:5d} IDh-H={b['IDh']-b['H']:5d} LB={b['LB']:7d} I>={b['Ilb']:8.1f} I/n^2={b['Ilb']/n**2:.3f}")
