#!/usr/bin/env python3
"""Finite checks for BELOW_EIGHT_THIRDS.md, not a puzzle solver or proof.

Uses only the standard library. The pipeline has unlimited placeholder supply;
it tests stock bookkeeping, NOT finite reserve feasibility or concentration.
"""

from collections import Counter
from itertools import product
from random import Random


def grouped_route(src, dst, b):
    """At most two monotone segments; gateways are near group boundaries."""
    lo = dst // b * b
    hi = lo + b - 1
    gateway = lo if src < lo else hi if src > hi else src
    return [(a, z) for a, z in ((src, gateway), (gateway, dst)) if a != z]


def check_routes():
    checked = 0
    for g, b in product(range(1, 13), repeat=2):
        k = g * b
        # Span units are block widths. One parallel band, one coordinate.
        coarse_span = sum(t * b + k - (t + 1) * b for t in range(g))
        fine_span = sum(b - 1 for _ in range(k))
        assert coarse_span + fine_span == k * (g + b - 2)
        for src, dst in product(range(k), repeat=2):
            path = grouped_route(src, dst, b)
            assert sum(abs(z - a) for a, z in path) == abs(dst - src)
            assert len(path) <= 2
            if path:
                assert path[0][0] == src and path[-1][1] == dst
                assert all(path[i][1] == path[i + 1][0] for i in range(len(path) - 1))
            checked += 1
    return checked


class Pipeline:
    """A chain of prefix-shift pipes, served from last hop to first.

    Items are (intended_class, dirty). Initial None entries are untagged junk.
    A prefix push at p ejects index 0, shifts 1..p toward 0, and inserts at p.
    Clean departures become stock. Dirty departures increment D and disappear
    into an unmodelled free pool. The first hop always has its scheduled tile.
    """

    def __init__(self, lengths, classes):
        self.pipes = [[None] * size for size in lengths]
        self.classes = classes
        self.stock = [Counter() for _ in lengths]
        self.bypass = [Counter() for _ in lengths]
        self.dirty_in = [Counter() for _ in lengths]
        self.peak = [Counter() for _ in lengths]

    def in_flight(self, node):
        return Counter(item[0] for item in self.pipes[node - 1] if item is not None)

    def serve(self, cls, positions):
        for j in reversed(range(len(self.pipes))):
            dirty = False
            if j:
                if self.stock[j][cls]:
                    self.stock[j][cls] -= 1
                else:
                    self.bypass[j][cls] += 1
                    dirty = True
            pipe, p = self.pipes[j], positions[j]
            departed = pipe[0]
            pipe[:p] = pipe[1:p + 1]
            pipe[p] = (cls, dirty)
            if j + 1 < len(self.pipes):
                if departed is not None:
                    tag, was_dirty = departed
                    if was_dirty:
                        self.dirty_in[j + 1][tag] += 1
                    else:
                        self.stock[j + 1][tag] += 1
                for tag, count in self.in_flight(j + 1).items():
                    self.peak[j + 1][tag] = max(self.peak[j + 1][tag], count)
        self.check()

    def check(self):
        for j in range(1, len(self.pipes)):
            flight = self.in_flight(j)
            for cls in range(self.classes):
                b, d = self.bypass[j][cls], self.dirty_in[j][cls]
                assert self.stock[j][cls] + flight[cls] + d == b
                assert b <= self.peak[j][cls] + d + 1
                assert d <= self.bypass[j - 1][cls]
                assert b <= sum(self.peak[i][cls] + 1 for i in range(1, j + 1))


def check_pipelines():
    histories = services = 0
    # Exhaustive two-pipe histories: both tags and both insertion positions.
    alphabet = tuple(product(range(2), range(2), range(2)))
    for history in product(alphabet, repeat=4):
        p = Pipeline([2, 2], 2)
        for cls, a, b in history:
            p.serve(cls, [a, b])
            services += 1
        histories += 1
    # Longer chains; bursts and uneven insertion depths create real shortages.
    rng = Random(20260928)
    for depth, mode, seed in product((2, 4, 8), range(3), range(10)):
        p = Pipeline([rng.randrange(1, 24) for _ in range(depth)], 7)
        for t in range(400):
            cls = rng.randrange(7) if mode == 0 else (t // 31 + seed) % 7
            positions = [rng.randrange(len(pipe)) if mode != 2 else
                         (len(pipe) - 1 if t % 29 else 0) for pipe in p.pipes]
            p.serve(cls, positions)
            services += 1
        histories += 1
    return histories, services


def check_cycle_reserves():
    # On a directed cycle, balanced removal requires r_i = r_(i-1).
    # Even one positive prescribed reserve then forces it at every vertex.
    checked = 0
    for vertices in range(2, 7):
        for removed in product(range(4), repeat=vertices):
            balanced = all(removed[i] == removed[i - 1] for i in range(vertices))
            assert balanced == (len(set(removed)) == 1)
            checked += 1
    return checked


def check_home_preload():
    """Check endpoint permutations only; Lean supplies legal 3-cycle paths.

    Blank is the last label/cell and is never in a cycle. Protected cells have
    their exact final tiles. Region demand ignores corridor cells.
    """
    rng = Random(13)
    trials = cycles = 0
    for _ in range(1000):
        regions, size = 9, 25
        total = regions * size
        board = list(range(total - 1))
        rng.shuffle(board)
        board.append(total - 1)
        corridors = {v * size + j for v in range(regions) for j in (0, 1)}
        cells = [[a for a in range(v * size, (v + 1) * size)
                  if a not in corridors and a != total - 1] for v in range(regions)]
        targets = [a for cs in cells for a in cs[:rng.randrange(12)]]
        protected = set()
        for a in targets:
            if board[a] != a:
                b = board.index(a)
                assert b not in protected
                c = next(x for x in range(total - 1)
                         if x not in protected and x not in (a, b))
                board[a], board[b], board[c] = board[b], board[c], board[a]
                cycles += 1
            protected.add(a)
            assert all(board[x] == x for x in protected)
        demand = [[0] * regions for _ in range(regions)]
        corridor_class = Counter(board[a] // size for a in corridors)
        for a, tile in enumerate(board[:-1]):
            src, dst = a // size, tile // size
            if a not in corridors and src != dst:
                demand[src][dst] += 1
        for v in range(regions):
            sends = sum(demand[v])
            recv = sum(row[v] for row in demand)
            # Blank's physical and target square coincide, so cancel here.
            assert recv - sends == 2 - corridor_class[v]
            assert max(0, recv - sends) <= 2
        trials += 1
    return trials, cycles


if __name__ == "__main__":
    print(f"Monotone grouped endpoint routes checked: {check_routes():,}")
    histories, services = check_pipelines()
    print(f"Pipeline histories: {histories:,}; completed services: {services:,}")
    print("Stock identity and additive shortage bounds passed after every service.")
    print(f"Cycle reserve removal vectors checked: {check_cycle_reserves():,}")
    trials, cycles = check_home_preload()
    print(f"Home preload trials: {trials:,}; endpoint 3-cycles: {cycles:,}")
    print("Protected targets and corridor-only demand imbalance checks passed.")
    print("No finite reserve, board embedding, concentration, or move bound is certified.")
