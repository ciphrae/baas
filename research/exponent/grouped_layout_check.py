#!/usr/bin/env python3
"""Check the disjoint-stripe embedding, not a legal puzzle move sequence."""
from itertools import product


def layout(b, h, core):
    k = b ** h
    q = 2 * ((h * b + 1) // 2)  # even: jumps over a strip then have odd length
    s, lanes, owner = q + core, {}, {}
    for axis, band, level in product(range(2), range(k), range(h)):
        parent_size = b ** (h - level)
        child_size = parent_size // b
        for parent in range(0, k, parent_size):
            for child in range(b):
                lo, hi = parent + child * child_size, parent + (child + 1) * child_size
                offset = level * b + child
                for direction, blocks in ((-1, range(lo - 1, parent - 1, -1)),
                                          (1, range(hi, parent + parent_size))):
                    key = axis, band, level, parent, child, direction
                    cells = []
                    for block in blocks:
                        active = range(s - 1, q - 1, -1) if direction == -1 else range(q, s)
                        for a in active:
                            along = block * s + a
                            cross = band * s + offset
                            cell = (cross, along) if axis == 0 else (along, cross)
                            assert cell not in owner, (cell, key, owner.get(cell))
                            owner[cell] = key
                            cells.append(cell)
                    lanes[key] = cells
                    # Adjacent virtual cells: ordinary step or odd strip jump.
                    for a, z in zip(cells, cells[1:]):
                        distance = abs(a[0] - z[0]) + abs(a[1] - z[1])
                        assert distance in (1, q + 1)
                        assert (sum(a) + sum(z)) % 2 == 1
                    for distance in range(len(blocks)):
                        # Farthest source-core cell has an affine insertion index.
                        pos = (distance + 1) * core - 1
                        assert pos < len(cells)
    expected = 2 * h * k * k * (b - 1) * core
    assert len(owner) == expected
    # Full stripe reservation includes unused gaps and intersections.
    stripe_area = k * k * (2 * q * s - q * q)
    assert len(owner) <= stripe_area <= 2 * k * k * q * s
    # A q-by-q stripe crossing is kept out of both pipe families.
    assert all(not (r % s < q and c % s < q) for r, c in owner)
    return len(lanes), len(owner)


if __name__ == '__main__':
    cases = lanes = cells = 0
    for b, h, core in product(range(2, 4), range(1, 4), (3, 4, 7)):
        a, z = layout(b, h, core)
        cases += 1
        lanes += a
        cells += z
    print(f'Layouts: {cases}; directed pipe pieces: {lanes:,}; occupied cells: {cells:,}')
    print('Disjointness, exact inventory, affine insertion slots, and odd-gap parity passed.')
    print('Endpoint access, staged insertion, reserve dynamics, and blank paths remain unproved.')
