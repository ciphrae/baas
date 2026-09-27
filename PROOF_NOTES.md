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
`f ≥ n²`; here `f(n) = n^(8/3) (log n)^(1/3)`) plus `O(n²)` estimates for
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
hub algorithm has `s ≈ k² log n` (`exists_finish_path_of`).

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
bound. Instead, for `n ≥ 3·2^25` take `k = 2m` with
`24·m³(log₂ n + 1) ≤ n < 24(m+1)³(log₂ n + 1)` and `s = ⌊n/k⌋`. The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix
(`Parberry/Prefix.lean`, `O(n²·k)`), and the remaining `k*s × k*s` board by the
hub algorithm. The residual board is reachable and its Manhattan distance
equals the original board's after the prefix (`Algorithm/Residual*.lean`,
`Hub/AsympBound.lean`). The existing cubic solver handles
`4096 ≤ n ≤ 3·2^25`, so the final theorem still starts at `4096`.

## Hub transport: departures from the paper's scheme

The paper's exponent `11/4` is the balance of Transport (`n³/k`) against the
`k³n` corridor tiles, each costing `O(n)` (Preparation, Arrangement). Corridors
pure in the full class need `k³n` cells, since each of `k²` classes must reach
`k²` squares. `SlidingPuzzle/Hub/` proves
`OPT(B) ≤ M(B) + O(n^(8/3) (log n)^(1/3))` with `O(k²n)` corridor cells: rows
sorted by target block column only, columns by exact class, and tiles turning
through the reservoir of a hub square. The pen-and-paper proof is
`research/exponent/PROOF.md` and the organization of the Lean proof
`research/exponent/LEAN_PLAN.md`; the main differences from the paper's scheme:

- **No Preparation, no Arrangement.** Corridors start with whatever tiles the
  board has there. A junk tile only moves toward the head of its corridor half
  and costs at most `n` before it drops into a reservoir; the `O(k²n log n)`
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
  than using probability theory.

The boardwise constant is now `894` for `n ≥ 4096`, down from `19,319`
at the start of the latest optimization pass, `20,816` before combined
accounting and the fractional in-flight budget, `27,508` before retaining
size-dependent budgets, `849,303` in an earlier version and
`4,828,800,024,144` originally. The asymptotic exponent is unchanged. The
certified estimates are:

- Three-cycles (`Moves/ThreeCycleSharp.lean`): on a board of side `n ≥ 6`, the
  blank is moved below the top-left corner (`≤ 2n`) and the three tiles are
  staged by the sharp Parberry placements (`≤ 8n` each) at `(0,1),(0,2),(0,3)`,
  or at `(0,1),(0,2)` when one of them already sits in the corner. A top-row
  three-cycle at the staged columns (24 moves) and the reversed staging give
  `≤ 52n` moves (`exists_three_cycle_sharp`), and a double swap `≤ 104n`. The
  previous staging used Zhong's general placement for the first tile and cost
  `254n` per three-cycle.
- Jumps: `Zhong.strip_jump` costs at most `12m + 1` moves on a `2 × m` strip,
  so a blank/tile jump over horizontal or vertical distance `d` costs
  `≤ 13(d+1)` (previously charged `25(d+1)`).
- Jumps (`Hub/OpJump.lean`): the blank jumps from `E` into `Z`, a three-cycle
  inside `Z`'s own `s × s` box puts a class-`y` tile on a second landing cell,
  the blank jumps back, and a third jump carries that tile to `E`. This costs
  `≤ 54s + 39s·d + 130 ≤ (s+3)(54 + 39d)`, `d = sqDist`, instead of a
  three-cycle in a box covering both squares (`65s(1+d)`).
- Operations (`IState.cost`): hop1 `55s + 26(k+1) + junkRow`, hop2
  `54s + 13k² + 65k + 78 + junkCol`, jump `(s+3)(54 + 39·sqDist)`. A
  relocation is a single jump when the squares are aligned (weight `54 + 39d`)
  and two jumps through the corner otherwise (weight `108 + 39d`); it costs
  `(s+3)` per weight unit. A bypass costs at most `(s+3)(39k + 15)`.
- Round walk: a cycle relocation serves at least two new squares, and along
  the snake order only row changes need a second jump, so a round weighs at
  most `66k² + 132k + 30 + (78k + 30)·#dummy` (`exists_round_events`).
- In-flight order: the lower tail uses weights `1 - g/(8K)` with
  `exp(-(134/125)v) ≤ 1 - v` on `[0, 1/8]`, so windows need only `8/7` of the
  expected pushes, and costs capacity `317kL ≤ s`. The upper tail uses weights
  `(9/8)^a`: since `(9/8)^17 ≥ e²`, at most `(17/16)μ + 6λ` insertions occur in a
  window, with `λ = 4L` and `L = log₂ n + 1`.
- In-flight budget: with `s ≤ k³`, `ln(kΔ) ≤ (7/4)ln n + 1/s²`, which gives
  `Rhub n = ⌊(14730nL + 13743n)/10000⌋ + 1`.
- Free tiles: home tiles pad the set-aside reserve only up to `Q'` tiles per
  square, so at most `k²(Rhub n + 8n + 10)` free tiles remain for cleanup.
- Cleanup (`Hub/Cleanup.lean`): a misplaced tile goes to its square in exchange
  for a wrong tile of that square, which goes home through a third wrong tile
  by one three-cycle, or, if it belongs where the first tile was, by a double
  swap. Each step removes at least two misplaced tiles: `52n(misplaced + 2n + 2)`.
- Whole hub algorithm (`AsympAccounting.lean`, `k ≥ 106`, `L ≥ 26`, capacity):
  `1000·hubBound ≤ 182251X + 255642Y`, with `X = n²s`, `Y = k²n²L`.
- Grid for `n ≥ 3·2^25`: `k = 2m` with `24m³L ≤ n < 24(m+1)³L`; then
  `m ≥ 53`, `8L ≤ 5m` (hence `s ≤ k³`), and `1268m²L ≤ n` (capacity). Cube
  scales: `(100000X)³ ≤ 146947³n⁸L`, `(10⁶Y)³ ≤ 480750³n⁸L`, `(350Z)³ ≤ n⁸L`.
- Natural logarithms: `L ≤ 1.496129 ln n` for `n ≥ 3·2^25`, whose cube root is
  at most `1.143729`.
- Initial range: for `4096 ≤ n ≤ 3·2^25`, the Parberry solver's exact bound
  `5n³ + 1509n² + 1505n + 4796` is at most `894·hubError n`, split at `2^20`,
  `2^25` and `2^26`.

Consequently the hub branch's real coefficient is
`1.143729·(2·1.46947·182.251 + 2·0.48075·255.642 + 2/350)`,
approximately `893.74`. Rounding upward gives `C = 894` (`hubLargeConstant_rounding`),
which also covers the initial range. `Hub.uniform_approximation_explicit`
exposes the numerical bound directly. This is a certified upper bound, not a
claim of optimality.

## Remaining structural improvements

The three-cycle constant `52` now drives most of the bound: hops (`55s`),
jumps (`52s` of `(54 + 39d)s`) and cleanup (`52n` per tile). In insertions and
jumps one of the three cycled cells is a free choice of reservoir cell; staging
from a reservoir corner with that tile already in place would save one of the
three placements. A jump or insertion could avoid the three-cycle altogether
if the wanted tile lay in the reservoir, but region tiles may also sit in the
landing strip and the own column piece, where corridor heads drop in. [OPTIMIZATION_IDEAS.md](OPTIMIZATION_IDEAS.md) lists this
and smaller remaining improvements. Removing the logarithm would require a
stronger in-flight argument; the simulations in `research/exponent/` suggest
that possibility but do not prove it.
