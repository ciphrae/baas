# Recursive halving vs. Zhong's corridors, counted by inefficient moves

Scripts (run with `uv run python <script>`): halving_model.py, rook_run.py, rook_run2.py,
rook_run3.py, queue_run.py, matched_run.py.

## Summary
1. Pure recursive halving is Θ(n³) inefficient on random boards and in the worst case, even
   with overhead-free transport: ≈ 0.4·n³ random, ≈ 0.65·n³ rot90. Loss is at the top levels:
   a crossing tile lands at a row of its target half unrelated to its target row (Θ(side)
   overshoot), and loops move tiles rigidly. Fits "≈ 2n³ length": length = M + 2·ineff ≈
   (2/3 + 0.8)·n³ on random boards.
2. One hybrid could improve the exponent to n^(8/3) (corridors homogeneous in one coordinate
   only) but the corner-supply problem is unresolved (section B).
3. Other hybrids give little: halving pre-sort of reservoirs (no first-order gain), halving
   for Preparation staging (capped by P's weight; 2-wide strip sorting is Θ(side) per tile),
   Finish (already lower order). Ring rotations solve rot90 cheaply but not the worst case.

## A. Pure halving (negative result)
- ineff = (length + ΔM)/2. First split: each wrong-half tile lands at a row independent of
  its target row, overshoot E[max(0,U−V)] = n/12 (U,V uniform on [0,n/2]) → ≥ n³/24 random,
  n³/12 rot180, before sideways error or loop overhead. Level with side h costs ∝ n²h:
  geometric series, first two levels carry about half.
- Loops are rigid: rotating by t moves every tile by t, so landing order follows start order;
  fixing it = sorting inside the strip.
- Sorting in 2-wide strips costs inversions, not Manhattan: n×2 OPT = I(B) + O(n log n);
  random OPT ≈ n² vs mean Manhattan ≈ (2/3)n² → gap ≈ h²/3 per strip, ≈ h/12 per tile.
- Idealized model (halving_model.py): only wrong-half tiles move, each directly to a vacated
  cell of its target half, charged its Manhattan detour (d(p,q)+d(q,t)−d(p,t))/2, no
  loop/blank overhead. ineff/n³:

| board | oblivious (16/32/64) | stable (16/32/64) | optimal matching (16/32) |
|---|---|---|---|
| random | .38/.38/.40 | .32/.37/.39 | .047/.037 |
| rot180 | .39/.42/.45 | .44/.47/.48 | 0 |
| rot90 | .55/.60/.61 | .61/.64/.65 | .21/.21 |
| transpose | .20/.22/.23 | .14/.15/.16 | 0 |

- rot90 cycles quadrants: every halving must move tiles sideways away from target columns;
  imbalance is not lower order in the worst case; split axis doesn't help by symmetry.
- Concentric ring rotations solve rot90 at ≈ 0 inefficiency (quarter-ring paths are monotone
  in both coordinates), but only that board.
- Target-aware landing to resolution δ needs δ-spaced homogeneous corridors = Zhong, k = n/δ.
- Practical: 0.65·n³ beats 8.45·n^(11/4) for n^(1/4) < 13 (n < ~28,600) on leading terms;
  with real lower-order terms halving wins at every practical size.

## B. Corridors homogeneous in one coordinate (possible n^(8/3), unresolved)
- A vertical corridor slide is efficient whenever the tile's target band lies ahead, whatever
  its target column. So vertical corridors need homogeneity in target band only, horizontal
  ones in target column block only: O(k²n) corridor tiles; Preparation/Arrangement O(k²n²);
  Transport ≈ A·n³/k; balance k ~ n^(1/3) → O(n^(8/3)). Side constraints hold (s ≥ k; crossing
  corridors O(k²) ≤ s iff k³ ≤ n; recursive Finish lower order).
- Why Zhong needs k³n: the corner. A transfer is one chain shift along an L-shaped path; the
  tile pushed around the corner must satisfy the second leg's homogeneity, so the first leg
  must be homogeneous in the full group; Zhong's first leg is vertical in the source strip:
  k² groups × k strips × n = k³n. Any single-blank chain with a long first leg pays this.
- Attempt 1 (rook_run*.py): axis-at-a-time transfers through an intermediate square. Needs a
  free cell in an intermediate square; none. Transpose: ≈ 0.78·n² stuck events at k = 8, each
  an O(n) carry → Θ(n³). Random boards only O(k²s) stuck events.
- Attempt 2 (queue_run.py, matched_run.py), most promising: row R(a',c) in band a' holds
  tiles whose target column block is c (any band); column C(c,a) only in target strip c,
  holding group (a,c). Transfer with blank at X = (a,c), source tile T of group (a,c) in band
  a': blank along C(c,a) to band a'; pick up a band-a tile F from R(a',c) inside block c
  (carry ≤ s); run along R(a',c) to T; T enters the row. Row multisets unchanged, long slides
  efficient, count run = Algorithm 4; pooled model: transpose needs 0 relocations. Catch: the
  row is a delay line (T enters far away, drifts one cell per transfer; F must already be in
  block c). Exact simulation: 60–99% of transfers found no band-a tile in block c; fetching
  cost extra/(n²s) of 0.5–1.3 for k = 3..5, growing with k.
- Possible fixes: program the rows for the known (deterministic) demand order; m rows per
  (band, block) (k²mn corridor tiles); a new buffering trick. Any fix reintroducing k²
  group-homogeneous rows per band gives k³n again.
- Effort very high (new partition, Transport, GroupEquivalent, Preparation, Arrangement for
  mixed corridors). Recommendation: pen-and-paper attempt at the corner-supply problem first.

## C–E (not recommended)
- C, halving pre-sort of reservoirs by exit direction: with the nearer-side rule the expected
  exit distance is already s/4; packing left-bound tiles into [0, s/2] still averages s/4; a
  gain would need FIFO export order, which Algorithm 4 doesn't give.
- D, halving/bulk sorting for staging: grouping is itself a sort, Θ(distance) per tile in
  narrow strips; even 7.5 → 3 would be worth ≈ 0.75 on the constant; no concrete route.
- E, halving as Finish: Finish is lower order at two levels; halving is Θ(s³) on a square.
