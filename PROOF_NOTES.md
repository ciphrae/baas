# Proof notes

How the formalization relates to Zhong (2023), the prior work it improves on:
which conventions and arguments it shares with the paper, and where the hub
algorithm departs from the paper's scheme. Printed page `p` of the source is
PDF page `p - 128`. The development history of these notes is in git.

## Conventions

| Paper | Formalization |
| --- | --- |
| Definition 1 (p. 130): boards, zero is the blank | `Board n := Cell n ≃ Tile n`, tile `0` is the blank (`Basic.lean`) |
| Definitions 2–3, Table 1 (p. 131): U/D/L/R name the tile's direction | A move is specified by the blank's destination (`Step`) |
| Target `BT(x,y) = (n*x+y+1) mod n²`, blank at `(n-1,n-1)` | `target`, checked by `target_apply_val`, `target_bottomRight` |
| Definition 7, Proposition 3 (p. 132): orbit and solvability criterion | `Reachable`; both directions proved (`OrbitParity`, `Bridge/Reachability`) |
| Definition 11 (p. 138): Manhattan distance excludes the blank | `manhattan` |
| Section 5 (p. 144): statistics over the reachable orbit | `averageOptimalLength`, `godsNumber` (zero for `n < 2`) |

## The statistical part

`Hub/AsympStats.lean` reduces both conclusions to a boardwise bound
`OPT(B) ≤ M(B) + C*f(n)` (`UniformApproximationWith f`, for any error scale
`f ≥ n²`; here `f(n) = n^(8/3)`) plus `O(n²)` estimates for
the orbit mean and maximum of `M`. The paper cites Parberry for the latter; here
they are proved (`Bridge/Statistics.lean`, using the `Zhong` library): each
nonblank tile is uniformly distributed over the orbit, giving mean
`(2/3)*n³ + O(n)`; `M ≤ n³` for every board (`DistanceEstimates.lean`); and a
reachable board with `M ≥ n³ - 3*n²` gives the matching lower bound.

These bounds suffice, but the exact reachable maximum is known (not
formalized): `n³ - n` for even `n` and `n³ - 2n + 1` for odd `n` (6 and 22 at
`n = 2, 3`). For the upper bound, apply `|p - t| ≤ |p - c| + |t - c|` about the
centre `c = (n-1)/2` to every label including the blank. This gives
`M ≤ 2S - |b - c| - (n-1)`, where `S = 2n*Σₓ|x - c|` and `b` is the blank's
cell; for even `n` also `|b - c| ≥ 1`. For attainment, take the half-turn
board (reachable, `M = n³ - 2n + 2` or `n³ - 3n + 2`) and walk the blank
monotonically from `(0,0)` to the centre. Each step pushes a tile away from a
target on the far side of the centre, so `M` increases by one per step.

**Factor two.** A legal move changes `M` by exactly one, so every path satisfies
`length + M(end) = M(start) + 2*inefficientMoves` (`Path.length_add_manhattan`).
The paper's bounds of the form `SOL ≤ D + α` (Section 5) need `2α` when `α` counts
inefficient moves: moving a tile and back from the target gives length 2, `D = 0`,
`α = 1`. The asymptotic statement is unaffected.

## Squares and Finish

The division into squares (Section 4.1, pp. 138–139) is defined in
`Algorithm/Partition.lean`: a board of side `n = k*s` is a `k × k` grid of
squares of side `s = side n k`, one per target group. The hub algorithm uses
it only for the squares and group membership (in `Hub/FinishGen.lean`); its
corridors and reservoirs are its own (`Hub/Layout.lean`). Group membership
excludes the blank; the blank's location is recorded separately.

**Finish.** Squares are not locally solvable in general. As permitted by
Section 3.2 (p. 137), each nonfinal square is solved up to one transposition,
which is paired with a transposition of two buffer tiles in the final square to
give an even permutation (`Finish.lean`). The blank is borrowed from the global
target corner. The final square is solvable because the whole board is
reachable (`Algorithm/ResidualReachability.lean`). The local solver is
abstract (`SolverBound`): its cost must hold for every board of side `s`.
The Parberry-style solver gives `5*s³ + O(s²)` moves (`Parberry/Solver.lean`).
The paper's squares have side `k³`; Finish needs only `8 ≤ s`
(`Partition.FDims`: `2 ≤ k`, `8 ≤ side n k`, `k * side n k = n`), since the
hub algorithm has `s ≥ 8k²` (`exists_finish_path_of`).

The Finish chain carries an inefficiency bound alongside the length bound
(`SolverBound`). The block embedding with borrowed labels is
target-compatible, so it preserves the potential change of every move
(`Path.exists_embedded_efficient`); relabeling two tiles for parity costs at
most twice the distance between their targets
(`Path.inefficientMoves_relabel_swap_le`); and the access conjugation only adds
twice the access length (`Path.exists_conjugated_efficient`).

## Arbitrary sides

The paper rounds `n` down to a fourth power, leaving up to `4*n^(3/4)` outer
layers whose Parberry prefix costs `60*n^(11/4)`, which would dominate the new
bound. Instead, for `n ≥ 2·10⁶` take `k = 2m` with `m` the largest integer
such that `304m²(log₂(2mn²) + 4) + 10m ≤ 5n` and `64m³ ≤ n`, and `s = ⌊n/k⌋`
(`Hub/LinBound.lean`). The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix
(`Parberry/Prefix.lean`, `O(n²·k)`), and the remaining `k*s × k*s` board by the
hub algorithm. The residual board is reachable and its Manhattan distance
equals the original board's after the prefix (`Algorithm/Residual*.lean`,
`Hub/AsympBound.lean`). The existing cubic solver handles
`4096 ≤ n ≤ 2·10⁶`, so the final theorem still starts at `4096`.

## Hub transport: departures from the paper's scheme

The paper's exponent `11/4` is the balance of Transport (`n³/k`) against the
`k³n` corridor tiles, each costing `O(n)` (Preparation, Arrangement). Corridors
pure in the full class need `k³n` cells, since each of `k²` classes must reach
`k²` squares. `SlidingPuzzle/Hub/` proves
`OPT(B) ≤ M(B) + O(n^(8/3))` with `O(k²n)` corridor cells: rows
sorted by target block column only, columns by exact class, and tiles turning
through the reservoir of a hub square. The pen-and-paper proof is
`research/exponent/PROOF.md` and the organization of the Lean proof
`research/exponent/LEAN_PLAN.md`; the main differences from the paper's scheme:

- **No Preparation, no Arrangement.** Corridors start with whatever tiles the
  board has there. A junk tile only moves toward the head of its corridor half
  and costs at most `n` before it drops into a reservoir; the `O(k²n)`
  tiles left outside their squares at the end are sent home at least two at a
  time, by a three-cycle or a double swap (`Hub/Cleanup.lean`, `O(n)` each).
- **Rounds instead of Algorithm 4.** The reservoir demand multigraph, padded
  with dummy edges and loops, splits into perfect matchings (Hall/König,
  `Hub/Plan.lean`); a round follows its cycles backwards, and cycles start in
  snake order so relocations cost `O(k²s)` per round (`Hub/RoundWalk.lean`).
- **Counts, not transpositions.** A transfer realizes a count update, not a
  transposition of two specific cells (a prescribed transposition can have the
  wrong parity). Reservoirs are tracked by class counts
  (`Algorithm/Transport/Counts.lean`), with roles (scheduled, stock, free,
  home) as ghost state (`Hub/Run*.lean`). Insertions are placed by
  three-cycles in local boxes, which avoids exit carries and their parity
  cases (`Hub/Op*.lean`).
- **A probabilistic ingredient.** Row halves are delay lines; the rounds are
  run in an order in which few tiles of each class are in flight. It exists
  by a subset Chernoff bound proved from Maclaurin's inequality
  (`Hub/Chernoff*.lean`, `Hub/InFlight*.lean`), counting permutations rather
  than using probability theory. A tile inserted from block distance `d`
  crosses the bands `d, d-1, …, 0` of its half, and leaves band `j` after `s`
  insertions from distances `≥ j` (`Hub/InFlightSegment.lean`). Its residence
  time is the sum of the band windows `w_j ≈ (4/3)sΔ/B_j`, where `B_j` counts
  the insertions from distances `≥ j`. Weighted by the insertion rates these
  sums telescope, `∑_d G_d ∑_{j≤d} 1/B_j = #{j : B_j > 0}`
  (`sum_mul_sum_inv_le`), so a hub has `O(n)` tiles in flight rather than
  `O(n log n)`, and the logarithm disappears from the bound. The tiles of one
  class are bounded over all distances together: the windows `[τ - W_d, τ]`
  end at the same time, so the rounds counted at each position form a chain,
  and a moment bound for nested sets (`Hub/ChernoffChain.lean`) gives one
  Chernoff slack per class instead of one per class and distance.

The boardwise bound is now `OPT(B) ≤ M(B) + 635·n^(8/3)` for `n ≥ 4096`
(`1084` before local operations were charged by displacement). In the older scale
`n^(8/3)(log n)^(1/3)` the coefficient went `4,828,800,024,144` originally,
`849,303` in an earlier version, then `19,319`, `894` and `776` in the
optimization passes. The certified estimates are:

- Inefficiency by displacement: `2·inefficient = length + M(end) - M(start)`, so
  a path that only moves the tiles of a set `U` has
  `2·inefficient ≤ length + Σ displacement` (`Path.two_inefficientMoves_le_of_displacement`),
  and a path ending at the target has `2·inefficient ≤ length`.
- Three-cycles (`Moves/ThreeCycleSharp.lean`): staging by the sharp Parberry
  placements (`≤ 8n` each), a top-row three-cycle and the reversed staging give
  `≤ 52n` moves (`exists_three_cycle_sharp`). In a box of side `s` the three
  tiles move at most `4s` in total, so at most `28s` moves are inefficient
  (`exists_box_three_cycle_ineff`).
- Jumps: `Zhong.strip_jump` costs at most `12m + 1` moves on a `2 × m` strip,
  so a blank/tile jump over distance `d` has length `≤ 13(d+1)`; it moves one
  tile, so at most `7(d+1)` moves are inefficient (`exists_hjump_step`).
- Jumps (`Hub/OpJump.lean`): the blank jumps from `E` into `Z`, a three-cycle
  inside `Z`'s box puts a class-`y` tile on a second landing cell, the blank
  jumps back, and a third jump carries that tile to `E`:
  `≤ 30s + 21s·d + 70 ≤ (s+3)(30 + 21d)`, `d = sqDist`.
- Operations (`IState.cost`): hop1 `31s + 14(k+1) + junkRow`, hop2
  `30s + 7k² + 35k + 42 + junkCol`, jump `(s+3)(30 + 21·sqDist)`. A relocation
  weighs `30 + 21d` when aligned and `60 + 21d` through a corner; a bypass costs
  at most `(s+3)(21k + 9)`.
- Round walk: a round weighs at most `36k² + 72k + 18 + (42k + 18)·#dummy`
  (`exists_round_events`).
- In-flight order: the lower tail uses weights `1 - g/(4K) ≥ (3/4)^(g/K)`, with
  exponent `0.03423` and capacity `76kλ_A ≤ 5s`, `λ_A = log₂(k³s²) + 4`; the
  upper tail counts the class-`x` tiles of a half over all distances at once
  (nested sets, `card_upper_tail_chain`), at most `(41/40)μ + 15λ`.
- In-flight budget: per hub at most
  `(41/30)(n + 2k) + (41/20)k(k+1) + 90k(log₂ n + 1)`; with capacity and
  `k ≥ 50` this is `Rhub n = ⌊143n/100⌋ + 1`.
- Cleanup (`Hub/Cleanup.lean`): a three-cycle fixes two misplaced tiles and a
  double swap four, in length `26n(misplaced + 2n + 5)`. Cleanup and Finish end
  at the target, so together they are charged half their length (`Transport.lean`).
- Whole hub algorithm (`AsympAccounting.lean`, `k ≥ 50`, `668k ≤ s`):
  `1000·hubBound ≤ 101960X + 367100W`, with `X = n²s`, `W = k²n²`.
- Grid for `n ≥ 2·10⁶` (`LinBound.lean`): `m ≥ 25`, and `m ≥ 26` from
  `2.1·10⁶`; for `n ≥ 2.3·10⁶` either `n < 64(m+1)³` or capacity fails at
  `m + 1`, where `log₂(2(m+1)n²) + 4 ≤ 0.395x` (`lin_log_le`), so
  `0.1964x ≤ m ≤ x/4` (`lin_range`).
- Real bound (`LinError.lean`): `KX x³ + 8KW m³ ≤ 634.8·1000·m x²` on each range,
  by concavity in `m` (`lin_core_of`, `lin_core_25`, `lin_core_26`, `lin_core`);
  the prefix adds at most `0.128x⁸`.
- Initial range: for `4096 ≤ n ≤ 2·10⁶`, the Parberry solver's exact bound
  `5n³ + 1509n² + 1505n + 4796` is at most `635·n^(8/3)` (`cubic_le_linError`).

Consequently `OPT(B) ≤ M(B) + 635·n^(8/3)` for every `n ≥ 4096`
(`Hub.uniform_approximation_explicit`). The coefficient is set near `2·10⁶`,
where capacity limits `k`; asymptotically the grid ratio `k/n^(1/3) = 1/2`
gives `2(2A + B/4) ≈ 591`. These are certified upper bounds, not claims of
optimality.

## Remaining structural improvements

Hops (`62` of `A = 101.96`) and relocations (`36`) dominate the transport side;
cleanup (`13n` per misplaced tile, `≈ 232` of `B = 367.1`) the corridor side.
[OPTIMIZATION_IDEAS.md](OPTIMIZATION_IDEAS.md) lists the remaining improvements.
