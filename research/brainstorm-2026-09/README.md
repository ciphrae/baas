# Brainstorm: lowering the n^(11/4) constant (and the exponent)

Four parallel analyses (halving, Preparation, global structure, lower bounds).
Nothing here is formalized; numbers are hand derivations plus small simulations.
Scripts: tmp/{halving,prep,structure,bounds}/.

Constant = (4/3)·A^(3/4)·(3P)^(1/4); today A = 3.5 (Transport), P = 12.5
(Preparation 11.5 + Arrangement 1), constant 8.45.

## Concrete, compatible improvements (ranked)

| # | Idea | Effect | Effort / risk |
|---|---|---|---|
| 1 | Exit-and-restore: after the carry, walk back along T's row to undo the shift; wrong tiles never change column, so charge per reservoir cell (≤ s extractions per column) instead of per transfer | A 3.5 → 2.75, constant 8.45 → ~7.05 | moderate (strip word + new potential; look-ahead proof deleted) / low |
| 2 | Arrangement as a "drain" run: transfers with zero exit distance, every long slide moves a tile toward home; rounds by band distance keep it balanced | P 12.5 → 11.5 (Arrangement → lower order) | moderate / low |
| 3 | Preparation by long-range conveyor families (assignment plan, local gather, column conveyor, turn, row conveyor, park) | Preparation 11.5 → ~4/3 | high (≈ size of current Preparation) / low–medium |
| 4 | Same-band sources: vertical exit into H_i | A 2.75 → ~2.65 | moderate, only after 1 |

Combined 1+2+3: A ≈ 2.75, P ≈ 4/3 → constant ≈ 4.0.
Deeper Preparation variants (Transport flushes dirty corridors; adaptive corridors) reach
P ≈ 1/3–2/3 but mean rewriting Transport's core. Structural floor for Preparation in this
architecture: ≈ 2/3 (neighbour-derangement board).

## Recursive halving (speedsolving method)

Θ(n³) inefficient moves: ~0.4·n³ random, ~0.65·n³ rot90 in an idealized overhead-free model,
0.21·n³ on rot90 even with optimal landing cells. Cause: a tile crossing a midline lands at a
row unrelated to its target row, and loops move tiles rigidly. rot90 cycles the quadrants.
Useful as a practical solver (beats 8.45·n^(11/4) for n below ~28,600 on leading terms),
not for the asymptotic bound; making it target-aware turns it into Zhong's corridors.

## Exponent

- Known: n² ≲ worst-case inefficiency ≲ n^(11/4); row mirror forces ≥ n² − O(n); standard
  lower-bound tools cap at O(n²); no published improvement of Zhong's exponent found.
- 11/4 = balance of Transport n³/k and corridor filling k³n².
- Candidate: corridors homogeneous in one coordinate only (O(k²n) corridor tiles) → n^(8/3).
  Blocker: at the corner of the L-shaped route the tile must match the second leg's group;
  two attempts failed in simulation (transpose gets stuck; matched-exchange rows miss 60–99%).
  Research question; pen-and-paper attempt before any Lean.
  **Resolved on branch `exponent-research`:** hub transport with a random-like round order
  gives `O(n^(8/3) (log n)^(1/3))`, fully formalized (`research/exponent/`, `SlidingPuzzle/Hub/`).
- Shared corridors per target band (n^(8/3) or n^(5/2) heuristics) fail at the junction with H_i.

## Side results

- God's number ≥ n³ + n² − O(n) (inversion distance on rot180), no printed source found.
- Exact: 3×3 max inefficiency 9; 4×4 transpose needs 16 = n² (rigorous bounds give 0), rot90 needs 1.

## Check of exit-and-restore (main session)

With the walk-back, wrong reservoir tiles move only vertically in the blank's column
(entry slides) and never change column, and each extracted tile was wrong from the start
(count moves go off-diagonal → diagonal). So a reservoir column supplies at most `s`
extractions. A tile at column offset `x` costs at most `4·min(x, s−x)` for its exit
(nearer side) plus `max(x, s−x)` for the next transfer's horizontal travel inside its
square, i.e. `s + 3·min(x, s−x)`; the average over columns is `1.75·s`. With `s` for entry
and vertical travel, `A = 2.75`. The per-transfer optimum `2.5·s` in PROOF_NOTES assumed a
fresh adversarial tile position every transfer, which the per-cell budget rules out.
Details: structure/REPORT.md, structure/restore.py.

## Plan

1. Exit-and-restore (A 3.5 → 2.75, constant ≈ 7.05).
2. Drain Arrangement (Arrangement lower order).
3. Conveyor-family Preparation (Preparation 11.5 → ≈ 4/3; with 1 and 2, constant ≈ 4.0).
Separately, a pen-and-paper look at the corner-supply problem (n^(8/3)): done, see above.

Per-angle reports: halving/, prep/, structure/, bounds/ (REPORT.md in each).
