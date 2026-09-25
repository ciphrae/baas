"""Hill-climb (simulated annealing) over boards to maximise the combined admissible lower bound
on inefficiency, Ilb = (max(V+2LCr, IDv) + max(H+2LCc, IDh) - M)/2.  Also a variant maximising LB itself
(God's number lower bound)."""
import random, sys, math
from lb import bounds, sym_board, fix_parity, reachable

def run(n, start, obj, iters, seed):
    rnd = random.Random(seed)
    B = dict(start)
    cells = list(B)
    cur = obj(bounds(n, B))
    best, bestB = cur, dict(B)
    T0 = 2.0
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        # a 3-cycle of non-blank tiles preserves parity
        a, b, c = rnd.sample([x for x in cells if B[x] != 0], 3)
        B[a], B[b], B[c] = B[c], B[a], B[b]
        v = obj(bounds(n, B))
        if v >= cur or rnd.random() < math.exp((v - cur) / T):
            cur = v
            if v > best:
                best, bestB = v, dict(B)
        else:
            B[a], B[b], B[c] = B[b], B[c], B[a]
    return best, bestB

if __name__ == '__main__':
    n = int(sys.argv[1]); iters = int(sys.argv[2]); mode = sys.argv[3]
    obj = (lambda b: b['Ilb']) if mode == 'I' else (lambda b: b['LB'])
    for s in ['mirror', 'rot180', 'flip']:
        start, _ = fix_parity(n, sym_board(n, s))
        best, B = run(n, start, obj, iters, 1)
        assert reachable(n, B)
        b = bounds(n, B)
        print(n, mode, s, 'best', best, 'per n^2', round(best / n**2, 3), {k: b[k] for k in ('M', 'LCr', 'LCc', 'IDv', 'IDh', 'V', 'H', 'LB')}, 'n^3+n^2-2n-2 =', n**3 + n*n - 2*n - 2)
        if n <= 6:
            for x in range(n):
                print('   ', ' '.join(f"{B[(x, y)]:3d}" for y in range(n)))
