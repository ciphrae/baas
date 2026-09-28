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
bound. Instead, for `n ≥ 1.1·10⁹` take `k = 2m` with `m` the largest integer
such that `304m²(log₂(2mn²) + 4) + 10m ≤ 5n` and `70m³ ≤ n`, and `s = ⌊n/k⌋`
(`Hub/LinBound.lean`). The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix
(`Parberry/Prefix.lean`, `O(n²·k)`), and the remaining `k*s × k*s` board by the
hub algorithm. The residual board is reachable and its Manhattan distance
equals the original board's after the prefix (`Algorithm/Residual*.lean`,
`Hub/AsympBound.lean`). The explicit bound starts at `1.1·10⁹`; the asymptotic
statements need only some start.

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

The boardwise bound is now `OPT(B) ≤ M(B) + 268·n^(8/3)` for `n ≥ 1.1·10⁹`
(`348` before designated relocations; the estimates below describe the `348`
version except that relocation legs now cost `(s+3)(16 + 7d)`, `A = 42.65`,
`B = 195.3`, `D = 267.8`)
(`583` before the smaller reserve, the junk count by half lengths and the
near-corner three-cycles; `635` from `n ≥ 4096`; `1084` before local operations
were charged by displacement). In the older scale
`n^(8/3)(log n)^(1/3)` the coefficient went `4,828,800,024,144` originally,
`849,303` in an earlier version, then `19,319`, `894` and `776` in the
optimization passes. The certified estimates are:

- Inefficiency by displacement: `2·inefficient = length + M(end) - M(start)`, so
  a path that only moves the tiles of a set `U` has
  `2·inefficient ≤ length + Σ displacement` (`Path.two_inefficientMoves_le_of_displacement`),
  and a path ending at the target has `2·inefficient ≤ length`.
- Placements (`Parberry/PlacementDist.lean`): every Parberry placement word has
  length `8d + 6v + c` in its offsets, so a placement costs at most
  `8·dist + 1` moves (`exists_placement_dist`), besides the uniform `8n`.
- Three-cycles (`Moves/ThreeCycleSharp.lean`): staging by the sharp Parberry
  placements (`≤ 8n` each), a top-row three-cycle and the reversed staging give
  `≤ 52n` moves (`exists_three_cycle_sharp`); cleanup uses these.
- Near-corner three-cycles (`Moves/ThreeCycleNear.lean`): when two of the three
  tiles and the blank are within `δ` of the top-left corner, only the third
  tile needs the uniform placement, so staging costs `8n + 81δ + 424` and the
  three-cycle `16n + 162δ + 872` (`exists_three_cycle_near`). In a box of side
  `s`, reflected so that any of its corners is the local corner
  (`boxEmbR`), at most `10s + 82δ + 436` moves are inefficient
  (`exists_box_three_cycle_near`).
- Insertions (`Hub/OpInsert.lean`): the corridor cell `v`, the blank's landing
  cell `w` and the spare reservoir cell lie within `δ ≤ 6k + 7` of a corner of
  the box (top left or right for hop1, top or bottom left for hop2), so an
  insertion costs `10s + 492k + 1010` after its jump. `HDims.big`
  (`600k + 2000 ≤ s`) absorbs the corner terms of the jump's cycle
  (`δ ≤ 6k + 12`, at most `11s`).
- Jumps: `Zhong.strip_jump` costs at most `12m + 1` moves on a `2 × m` strip,
  so a blank/tile jump over distance `d` has length `≤ 13(d+1)`; it moves one
  tile, so at most `7(d+1)` moves are inefficient (`exists_hjump_step`).
- Jumps (`Hub/OpJump.lean`): the blank jumps from `E` into `Z`, a near-corner
  three-cycle inside `Z`'s box puts a class-`y` tile on a second landing cell,
  the blank jumps back, and a third jump carries that tile to `E`:
  `≤ 13s + 21s·d + 70 ≤ (s+3)(13 + 21d)`, `d = sqDist ≥ 1`.
- Operations (`IState.cost`): hop1 `13s + 506k + 1024 + junkRow`, hop2
  `12s + 7k² + 527k + 1052 + junkCol`, jump `(s+3)(13 + 21·sqDist)`. A served
  tile is charged hop1 plus hop2 (`hopC = 25s + 7k² + 1033k + 2076`). A
  relocation weighs `13 + 21d` when aligned and `26 + 21d` through a corner; a
  bypass costs at most `(s+3)(21k + 9)`.
- Round walk: a round weighs at most `28k² + 55k + 18 + (42k + 18)·#dummy`
  (`exists_round_events`): `7` per served square, `21` per unit of snake distance.
- In-flight order: the lower tail uses weights `1 - g/(4K) ≥ (3/4)^(g/K)`, with
  exponent `0.03423` and capacity `76kλ_A ≤ 5s`, `λ_A = log₂(k³s²) + 4`; the
  upper tail counts the class-`x` tiles of a half over all distances at once
  (nested sets, `card_upper_tail_chain`), at most `(41/40)μ + 15λ`.
- In-flight budget: per hub at most
  `(41/30)(n + 2k) + (41/20)k(k+1) + 90k(log₂ n + 1)`; with capacity and
  `k ≥ 500` this is `Rhub n = ⌊1376n/1000⌋ + 1`.
- Reserve (`Hub/Run.lean`): the first `Q' = Rhub + 2n + k² + 6` rounds are set
  aside. Dummies and loops of these rounds at a square number at most
  `Δ0 - sends ≤ sqCorridor + cnt(Z, Z) + 1`, and the dummy budget of the run is
  the actual number of planned dummies, so this padding suffices.
- Misplaced tiles: corridor junk counted by the half lengths is at most
  `k²·sqCorridor ≤ 2k²n` (`junkCnt_le`), so at most `k²(Rhub + 2n + k² + 6) +
  2k²n` free tiles remain for cleanup.
- Cleanup (`Hub/Cleanup.lean`): a three-cycle fixes two misplaced tiles and a
  double swap four, in length `26n(misplaced + 2n + 5)`. Cleanup and Finish end
  at the target, so together they are charged half their length (`Transport.lean`).
- Whole hub algorithm (`AsympAccounting.lean`, `k ≥ 500`, `881k ≤ s`):
  `1000·hubBound ≤ 55650X + 251100W`, with `X = n²s`, `W = k²n²`.
- Grid for `n ≥ 1.1·10⁹` (`LinBound.lean`): `m ≥ 250`, `70m³ ≤ n`; the capacity
  condition holds at `m + 1` since `log₂(2(m+1)n²) + 4 ≤ 0.08x` (`lin_log_le`),
  so `0.2416x ≤ m ≤ 0.2427x` (`lin_range`).
- Real bound (`LinError.lean`): `KX x³ + 8KW m³ ≤ 347.7·1000·m x²` on this
  range, by concavity in `m` (`lin_core_of`, `lin_core`); the prefix adds at
  most `0.032x⁸`.

Consequently `OPT(B) ≤ M(B) + 348·n^(8/3)` for every `n ≥ 1.1·10⁹`
(`Hub.uniform_approximation_explicit`). The grid ratio `m/x ≈ 0.242` minimizes
`KX/c + 8KW c²` (`≈ 347.58`), so this is also the asymptotic value of the
accounting. These are certified upper bounds, not claims of optimality.

## Remaining structural improvements

Relocations (`28` of `A = 55.65`) and hops (`25`) make up the transport side;
cleanup (`13n` per misplaced tile, about `9.75k²n` tiles, `≈ 127` of
`B = 251.1`) and dummy relocations (`84`) the corridor side.
[OPTIMIZATION_IDEAS.md](OPTIMIZATION_IDEAS.md) lists the remaining improvements.
