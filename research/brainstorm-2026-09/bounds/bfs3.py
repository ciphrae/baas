"""Exact BFS for the 3x3 puzzle (and 2x2): distribution of I = (OPT - M)/2 over the reachable orbit."""
import sys
from collections import deque, Counter
from lb import target, goal_cell, sym_board, fix_parity, bounds

n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
cells = [(x, y) for x in range(n) for y in range(n)]
T = target(n)
start = tuple(T[c] for c in cells)

def neighbors(s):
    b = s.index(0)
    bx, by = divmod(b, n)
    for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        x, y = bx + dx, by + dy
        if 0 <= x < n and 0 <= y < n:
            j = x * n + y
            l = list(s); l[b], l[j] = l[j], 0
            yield tuple(l)

dist = {start: 0}
q = deque([start])
while q:
    s = q.popleft()
    d = dist[s]
    for t in neighbors(s):
        if t not in dist:
            dist[t] = d + 1
            q.append(t)

def M(s):
    return sum(abs(i // n - goal_cell(n, t)[0]) + abs(i % n - goal_cell(n, t)[1]) for i, t in enumerate(s) if t)

Ic = Counter()
maxI, arg = -1, []
maxOPT = max(dist.values())
for s, d in dist.items():
    I = (d - M(s)) // 2
    Ic[I] += 1
    if I > maxI:
        maxI, arg = I, [s]
    elif I == maxI:
        arg.append(s)
print('states', len(dist), 'God', maxOPT, 'max M', max(M(s) for s in dist))
print('I distribution', sorted(Ic.items()))
print('mean I', sum(k * v for k, v in Ic.items()) / len(dist))
print('max I', maxI, 'attained by', len(arg), 'e.g.', arg[:4], [(dist[a], M(a)) for a in arg[:4]])
gods = [s for s, d in dist.items() if d == maxOPT]
print('God positions', [(s, M(s), (dist[s] - M(s)) // 2) for s in gods])
for name in ['rot180', 'rot90', 'transpose', 'antitranspose', 'mirror', 'flip']:
    B, fixed = fix_parity(n, sym_board(n, name))
    s = tuple(B[c] for c in cells)
    b = bounds(n, B)
    print(name, 'fixed' if fixed else '', 'OPT', dist[s], 'M', M(s), 'I', (dist[s] - M(s)) // 2, 'I_lb', b['Ilb'])
