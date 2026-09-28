#!/usr/bin/env python3
"""Abstract many-level routes and matching traffic; no physical puzzle moves."""
from collections import Counter, defaultdict
from itertools import product
from random import Random


def route(src, dst, b, h):
    """Each segment is (level, parent_start, child, direction, start, end)."""
    parent, size = 0, b ** h
    out = []
    for level in range(h):
        child_size = size // b
        child = (dst - parent) // child_size
        lo = parent + child * child_size
        hi = lo + child_size - 1
        gateway = min(max(src, lo), hi)
        if src != gateway:
            out.append((level, parent, child, 1 if src < gateway else -1, src, gateway))
        src = gateway
        parent, size = lo, child_size
    assert src == dst
    return out


def check_geometry(b, h):
    k = b ** h
    classes = defaultdict(set)
    checked = 0
    for src, dst in product(range(k), repeat=2):
        path = route(src, dst, b, h)
        assert len(path) <= h
        assert sum(abs(seg[-1] - seg[-2]) for seg in path) == abs(dst - src)
        if path:
            assert path[0][-2] == src and path[-1][-1] == dst
            assert all(a[-1] == z[-2] for a, z in zip(path, path[1:]))
        for level, parent, child, direction, a, z in path:
            classes[level, parent, child, direction].add(dst)
        checked += 1
    for level in range(h):
        parent_size = b ** (h - level)
        child_size = parent_size // b
        # Lane lengths count block-width cells; directions occupy disjoint sides.
        span = sum(child * child_size + parent_size - (child + 1) * child_size
                   for _parent in range(0, k, parent_size) for child in range(b))
        assert span == k * (b - 1)
        # Multiply by k target rows and k parallel source bands.
        active_classes = k * k * sum(len(ds) for lane, ds in classes.items() if lane[0] == level)
        assert active_classes <= 2 * k ** 3
        # Each lane has <= k insertions/round and <= parent_size distance bands.
        # A coarse upper bound for all per-round rounding terms at this level:
        directed_lanes = 2 * (k // parent_size) * b * k
        rounding_budget = directed_lanes * k * parent_size
        assert rounding_budget == 2 * k ** 3 * b
    return checked


def check_matching(b, h, kind):
    k = b ** h
    sources = list(product(range(k), repeat=2))
    if kind == 'transpose':
        targets = [(c, r) for r, c in sources]
    elif kind == 'reverse':
        targets = [(k - 1 - r, k - 1 - c) for r, c in sources]
    else:
        targets = sources[:]
        Random(1000 * b + 10 * h).shuffle(targets)
    counts, tags = Counter(), set()
    for (r, c), (u, v) in zip(sources, targets):
        # Horizontal lanes belong to source-row band; vertical to target-column band.
        # Include the band in the key: aggregating bands would misreport physical loads.
        for axis, band, src, dst in ((0, r, c, v), (1, v, r, u)):
            for seg in route(src, dst, b, h):
                lane = (axis, band) + seg[:4]
                counts[lane] += 1
                tag = (lane, (u, v))
                assert tag not in tags
                tags.add(tag)
    assert max(counts.values(), default=0) <= k
    return len(sources)


if __name__ == '__main__':
    endpoints = requests = 0
    for b, h in product(range(2, 5), range(1, 5)):
        endpoints += check_geometry(b, h)
        for kind in ('transpose', 'reverse', 'random'):
            requests += check_matching(b, h, kind)
    print(f'Hierarchical endpoint routes checked: {endpoints:,}')
    print(f'Permutation demands checked: {requests:,}')
    print('Monotonicity, depth, lane spans, class budgets, and round multiplicities passed.')
    print('No board embedding, residence bound, or finite-reserve schedule is certified.')
