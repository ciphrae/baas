# Proof notes

How the formalization relates to Zhong (2023), the prior work it improves on:
which conventions and arguments it shares with the paper, where the tree
algorithm departs from the paper's scheme, and the certified estimates behind
the constants. Printed page `p` of the source is PDF page `p - 128`. Earlier
versions of this project (an `O(n^(8/3))` bound by transport through hub
squares) are in git history.

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
`f ≥ n²`; here `f(n) = n^(5/2) (ln n)^(3/2)`, `Tree/Stats.lean`) plus `O(n²)`
estimates for the orbit mean and maximum of `M`. The paper cites Parberry for
the latter; here they are proved (`Bridge/Statistics.lean`, using the `Zhong`
library): each nonblank tile is uniformly distributed over the orbit, giving
mean `(2/3)*n³ + O(n)`; `M ≤ n³` for every board (`DistanceEstimates.lean`);
and a reachable board with `M ≥ n³ - 3*n²` gives the matching lower bound.

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
squares of side `s = side n k`, one per target group. Lanes and reservoirs are
the algorithm's own (`Tree/Layout.lean`, `Hub/Layout.lean`). Group membership
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
(`Partition.FDims`), and the tree algorithm has `s ≥ 2048k`.

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
bound. Instead, for a grid of `k` squares per side take `s = ⌊n/k⌋`
(`Tree/AsympBound.lean`). The outer `d = n - k*s < k` rows and columns are
solved by the Parberry prefix (`Parberry/Prefix.lean`, at most
`2(15n² + 3002n + 1)·k` inefficient moves, less than `n³/(64k)` here), and the
remaining `k*s × k*s` board by the tree algorithm. The residual board is
reachable and its Manhattan distance equals the original board's after the
prefix (`Algorithm/Residual*.lean`).

## Tree transport: departures from the paper's scheme

The paper's exponent `11/4` is the balance of Transport (`n³/k`) against the
`k³n` corridor tiles, each costing `O(n)` (Preparation, Arrangement). Corridors
pure in the full class need `k³n` cells, since each of `k²` classes must reach
`k²` squares. The tree algorithm (`SlidingPuzzle/Tree/`) uses `O(k·q·n)` lane
cells, `q ≈ h·b` offsets for branching `b` and depth `h`, and routes each tile
in at most `h` hops per axis. Transport and Finish cost `O(h·n³/k)`, the lanes
`O(k·q·n²)`; with `k = b^h` the balance `s ≈ 8h·b·k` gives the exponent
`5/2 + 1/(4h+2)`. The design is described in
[research/exponent/TREE_PLAN.md](research/exponent/TREE_PLAN.md); the main
differences from the paper's scheme:

- **No Preparation, no Arrangement.** Lanes start with whatever tiles the
  board has there. A junk tile only moves toward the head of its lane and
  costs at most `n` before it drops into a square; the tiles left outside their
  squares at the end are sent home at least two at a time, by a three-cycle or a
  double swap (`Hub/Cleanup.lean`, `O(n)` each).
- **A hierarchy of lanes** (`Tree/LaneSys.lean`, `Tree/HierMix.lean`). Lane
  pieces of offset `(ℓ, i)` cover, inside each node of level `ℓ`, the blocks on
  either side of child `i`; a hop lands at the near end of the child containing
  the target. The branching may differ between levels, which the grid choice
  uses to fit `k` to `n` without a rounding loss that grows with `h`.
- **Rounds instead of Algorithm 4.** The demand multigraph, padded with dummy
  edges, splits into perfect matchings (Hall/König, `Hub/Plan.lean`); a round
  serves each edge along its route backwards, and relocations between cycles
  follow snake order (`Hub/RoundWalk.lean`, `Tree/RunReloc.lean`).
- **Placeholders.** A gateway without a clean stock tile for the destination
  inserts a free tile tagged with it, so every planned insertion happens and the
  traffic of a round depends on the round only (`Tree/RunServe.lean`). The stock
  identity bounds placeholders by the in-flight maxima, `Σ B ≤ (2h+1) Σ c`
  (`Tree/RunRank.lean`).
- **Preloaded home reserves** (`Tree/Preload.lean`). Before the plan,
  three-cycles put into every square the home tiles it needs as reserve for
  placeholders and dummy edges.
- **Counts, not transpositions.** A transfer realizes a count update, not a
  transposition of two specific cells (a prescribed transposition can have the
  wrong parity). Squares are tracked by class counts
  (`Algorithm/Transport/Counts.lean`), with roles (scheduled, stock, free,
  home) as ghost state (`Tree/RunGhost.lean`). Insertions are placed by a jump
  and a three-cycle in the square's box (`Tree/OpInsert.lean`).
- **A probabilistic ingredient.** Lanes are delay lines; the rounds are run in
  an order in which few tiles of each tag are in flight. It exists by a subset
  Chernoff bound proved from Maclaurin's inequality (`Hub/Chernoff*.lean`),
  counting permutations rather than using probability theory. A tile inserted
  from block distance `d` crosses the distance bands of its lane and leaves band
  `j` after `s` insertions from distances `≥ j`; weighted by the insertion rates
  these residence times telescope (`Hub/InFlightSegment.lean`,
  `Hub/InFlightSum.lean`, `Tree/Residence.lean`), so the in-flight budget of a
  lane is linear in its length, with one logarithmic Chernoff slack per tag.

## Certified estimates

- Inefficiency by displacement: `2·inefficient = length + M(end) - M(start)`, so
  a path that only moves the tiles of a set `U` has
  `2·inefficient ≤ length + Σ displacement` (`Path.two_inefficientMoves_le_of_displacement`),
  and a path ending at the target has `2·inefficient ≤ length`.
- Placements (`Parberry/PlacementDist.lean`): every Parberry placement word has
  length `8d + 6v + c` in its offsets, so a placement costs at most
  `8·dist + 1` moves (`exists_placement_dist`), besides the uniform `8n`.
- Three-cycles (`Moves/ThreeCycleSharp.lean`): staging by the sharp Parberry
  placements (`≤ 8n` each), a top-row three-cycle and the reversed staging give
  `≤ 52n` moves (`exists_three_cycle_sharp`); the preload and cleanup use these.
- Jumps: `Zhong.strip_jump` costs at most `12m + 1` moves on a `2 × m` strip,
  so a blank/tile jump over distance `d` has length `≤ 13(d+1)`; it moves one
  tile, so at most `7(d+1)` moves are inefficient (`exists_hjump_step`).
- Hops (`Tree/RunDefs.lean`): a hop along a lane costs at most
  `hopK = 20s + 20k(q+2) + 600k + 2000` plus one move per junk tile it shifts
  (`cost_hopEv`); a tile makes at most `2h` hops.
- Relocations (`Tree/RunReloc.lean`): one jump between aligned squares, two
  through a corner, at most `3(s+3)` per unit of relocation weight; a round
  weighs `15k² + 30k + 18` plus terms for dummy edges.
- Budgets (`Tree/RunAux.lean`, `Tree/AsympAccounting.lean`): lane cells
  `≤ 2k²qs`, total need `≤ 4k²qs + (14 + 30λ)k³q`, total reserve
  `≤ 6k²qs + (14 + 30λ)k³q + 6k²`, with `λ = 3(log₂ n + 1)`.
- The whole algorithm on side `k*s` (`Tree/Transport.lean`, `treeBound`): the
  preload at `52n` per reserve tile, the run, then cleanup (`26n` per misplaced
  tile) and Finish (`5s³` per square), the last two halved since they end at the
  target.
- Accounting (`Tree/FineAccounting.lean`): with `8kq ≤ s`, `16kλ ≤ s` and
  `2048·h·k ≤ s`, `treeBound ≤ 50(h+3)·k²s³`. Per `k²s³`: hops `40h`, plus `5h`
  for their lane-width terms, relocations `≈ 45`, preload `≈ 51`, cleanup
  `≈ 29`, stock `≈ 1.5h`, Finish `2.5`.
- Conditions (`Tree/Final.lean`, `optimalLength_le_lanes`): `8k²q ≤ n`,
  `256h ≤ q ≤ k` and `2λ ≤ q` give all of them; the last holds for branching
  `b ≥ 256` (`log_slack_mix`).
- Grid (`Tree/MixGrid.lean`): branching `b + 2` at the first `j` levels and `b`
  below. With `b` the largest even number such that `8h·b^(2h+1) ≤ n` and `j`
  the largest such that `8qk² ≤ n`, the next `j` fails, so
  `n·b² ≤ 8h(b+2)³k²` and `n³/k ≤ 1.012·√(8h)·n^(5/2+1/(4h+2))`. With the
  prefix this gives `102(h+3)√(8h)·n^(5/2+1/(4h+2))` for `n ≥ 8h·256^(2h+1)`.
- Accounting against the slack (`Tree/FineLog.lean`, `Tree/FinalLog.lean`):
  with only `8kq ≤ s`, `16kλ ≤ s`, `λ ≥ 64` and `k ≥ 64`,
  `treeBound ≤ (48h + 142)·k²s³` (hops and stock `≈ 47.8h`, preload `≈ 51.3`,
  relocations `≈ 57.2`, cleanup and Finish `≈ 32`); the reserve fits once
  `4h ≤ λ` (`optimalLength_le_lanes_log`).
- Depth and grid (`Tree/LamGrid.lean`): the smallest `h` with `h(b_h + 2) ≤ 2λ`,
  `b_h` the largest even `b` with `16λ·b^(2h) ≤ n`, then the largest `j` with
  `16λk² ≤ n`. Then `q ≤ 2λ`, `n < 25λk²`, and minimality gives a branching
  `b ≥ 73` at depth `h - 1` (`b^12 < 2^(b+2)`, `branch_large`), so
  `73^(2(h-1)) ≤ n` and `b_h ≥ 8`.
- Constants (`Tree/LamLog.lean`): the error is at most
  `(1 + 10(48h+142)√λ)·n^(5/2) ≤ (117 ln n + 4100)·√(ln n)·n^(5/2)` for
  `n ≥ 2²³`, using `ln 73 ≥ 4.28` and `λ ≤ 4.3281·ln n + 3`; hence
  `375·n^(5/2)·(ln n)^(3/2)`.

These are certified upper bounds, not claims of optimality.
[OPTIMIZATION_IDEAS.md](OPTIMIZATION_IDEAS.md) lists the remaining improvements.
