# Proof notes

How the formalization relates to Zhong (2023), where it departs from the printed
argument, and where the constant could be improved. Printed page `p` of the
source is PDF page `p - 128`. The development history of these notes is in git.

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

`Proposition9.lean` reduces both conclusions to a boardwise bound
`OPT(B) ≤ M(B) + C*n^(11/4)` (`UniformApproximation`) plus `O(n²)` estimates for
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

## The algorithm on admissible boards

The partition (Section 4.1, pp. 138–139) is defined directly in
`Algorithm/Partition.lean`, including the vertical corridor column
`b_i*k³ + j` exactly as printed. Group membership excludes the blank; the phase
states (`Algorithm/PhaseStates.lean`) record the blank's location separately.

**Departure: two rows per horizontal corridor.** The paper's `H_i` is row
`b_i` of the band `a_i` of square `i`. Here `H_i` has a second row, row `k+b_i`
of the band below (cyclically, so the last band's second rows lie in the first
band). Each band starts with `2k` corridor rows: its own groups' upper rows,
then the lower rows of the band above; vertical corridors and reservoirs lose
`k` rows. A transfer can then leave its reservoir through the side facing the
source: upward through the upper row, downward through the lower row, which
lies just below the band's reservoirs. The corridor quotas grow by `n` tiles
per group, which only changes lower-order terms.

**Generalization.** The paper uses `n = k⁴` and squares of side `k³`. Nothing
in the construction needs the square side to be exactly `k³`: it needs room
for `2k` horizontal corridor rows and `k²` vertical corridor columns per square,
and for the compressed staging area of width `k³`. So the partition is stated
for squares of side `s = side n k = n/k` subject to `Dims n k`: `2 ≤ k`,
`k³ ≤ s` and `k*s = n`. Every phase is proved in this generality, with costs
of the form `A*k²s³ + C*k⁵s² + O(k*s³)`. Both monomials are the paper's `k¹¹`
when `s = k³`, but they scale differently in `k` for fixed `n`: `k²s³ = n³/k`
(Transport, Finish) and `k⁵s² = k³n²` (Preparation, Arrangement, which move
the `k³n` corridor tiles a distance of order `n`).

**Preparation.** Every group's corridor quota is staged in the first `k³`
columns and the first `2k²` rows (`Preparation/Staging.lean`), together with one
spare tile per nonfinal group in row `2k²`. Staged row `ρ` belongs in row
`ρ/(2k)*s + ρ%(2k)`, i.e. the corridor rows with bands compressed to height
`2k` (`stagedRow`). A mixed prefix solves the first `k³`
columns (transposed row solver) and then `2k²+1` rows (`Parberry/MixedPrefix.lean`),
toward any target that assigns the right groups (`Allocation.lean`). The spares
are translated into the last reservoir, where the count algorithm needs them for
its margins. The staged rows are spread into the horizontal corridors by a
descending row schedule, and the staged columns into the vertical corridors by
chunked column translations. Each column is moved in as many chunks as its own
distance requires (`exists_descending_column_schedule_var`).

**Transport.** Algorithm 4 is formalized as a count run on the reservoir matrix
(`Transport/Counts.lean`), which terminates after at most `n²` transfers, and
each transfer is realized by a legal path (`Transport/Realization.lean`).

- *Departure:* a transfer realizes the count update, not a transposition of two
  specific cells. A prescribed transposition can have the wrong parity, and the
  corridor slides permute labels within a group anyway. The invariant
  `GroupEquivalent` treats the blank as a tile of the moving group until it
  reaches the source reservoir.
- A transfer may also permute tiles inside a reservoir, since only counts
  matter. The blank first slides to the top or bottom row of its reservoir
  (`Transport/ReservoirSlide.lean`), so the entry jump crosses at most `2k`
  corridor rows.
- *Upper or lower row:* toward a source in a band above, the blank enters the
  upper row of `H_i` and travels up; toward a band below, the lower row and
  travels down. Either way every ordinary vertical slide moves a tile of group
  `i` toward its own band, so only the entry slide costs, at most `s`. Within
  the band, the row is chosen by the sum of the blank's and the tile's
  distances to it; the two sums add up to `2s`, so the smaller is at most `s`
  (`transportStepBoundAmortized_of_vertical_bound`, `verticalTransportBound`).
  The last band's lower row lies at the top of the board, so within the last
  band only the upper row is used, at most `2s`. At the exit it carries the source tile to the corridor side of the
  reservoir (`Transport/Carry.lean`), then exchanges it into the corridor with
  short jumps.
- Long straight corridor slides cost at most `s` inefficient moves: after the
  destination interval, every slide moves a tile toward its target
  (`Moves/Corridor.lean`, Fact 3).
- Restoring jumps are charged at half their length plus the jump distance
  (`Path.two_inefficientMoves_le_of_blank_swap`).
- *Nearer side:* the source tile is carried to whichever side of its reservoir
  is nearer: the left, through the square's own vertical corridor `V(j,i)`, or
  the right, through the corridor `V(j',i)` of the square `j'` to its right
  (`Transport/Step.lean`). Both corridors hold group `i`, and the exit is one
  orientation-free core (`exists_transport_restore_exit`) instantiated twice.
  Squares in the rightmost column have only the left side.

- *Exit by a three-row carry, and back:* the source tile `T` is at distance
  `d` from the corridor side. The blank walks to it along the row two away
  from `T`'s, pulls `T` into the middle row, and carries it back with five-move
  carries whose return trips alternate between the two outer rows
  (`Moves/ShiftCarry.lean`). Each return through the walked row undoes the
  walk's shift there, so the net effect is a rotation: the far row shifts by
  one cell and `T` lands next to the corridor. After `T` has been jumped into
  the corridor, the blank walks back along `T`'s row to `T`'s old cell, which
  undoes the rotation exactly for odd `d` (`Moves/RestoreCarry.lean`; the entry
  column is chosen to make `d` odd, and a corridor step first fixes the jump
  parity). The whole exit is then a blank/tile exchange with nothing else in
  the reservoir moved. It has length `7d+O(k²)` and moves only `T`, by `d+O(k²)`,
  so at most `4d+O(k²)` of its moves are inefficient. Carries that always
  return through the same row leave a net displacement of `3d` besides `T`'s,
  i.e. `5d` inefficient moves. For a walk-and-carry word, `4d` is optimal: the
  blank's non-push moves displace the other tiles by `d-1` in total, and the
  length is at least `6d-5`. Words are computed on an abstract strip `ℕ × ℕ` by
  their traces (`Moves/StripTrace.lean`), which turn into exact board effects.

- *Per-cell charge:* horizontal travel is inefficient only inside the square
  the blank starts from, so it costs the distance from the blank's column to
  that square's edge in the direction of travel
  (`exists_horizontal_transport_slide_dir'`), at most `max(o, s-o)` for the
  offset `o` of the blank's column. After the restoring exit the blank sits on
  the transported tile's old cell, and the misplaced tiles of every reservoir
  stay in their columns: the exit restores the source reservoir, and the
  blank's slide in its own reservoir is vertical (`exists_reservoir_slide_path`).
  So each misplaced reservoir tile in a column with offset `o` is charged
  once, when it is transported: its exit through the nearer side, `4*min(o, s-o)`,
  and the next transfer's horizontal travel from its cell, `max(o, s-o)`
  (`exitWeight`; in the last column of squares the exit is always to the left,
  `4*o`). The board potential `transportPotential` (`Transport/Potential.lean`)
  sums these weights over misplaced reservoir tiles and adds the blank's own
  horizontal weight. Each transfer lowers it by the transported tile's weight
  and raises it by the blank's new weight (`wrongPotential_transfer`), and the
  potentials telescope along the run (`exists_path_of_count_run_amortized`).
  Averaged over the columns of a square the weight is
  `s*(1 + 3/2 * 1/2) = 1.75*s`, since `min(o, s-o)` averages `s/4`
  (`four_sum_min_le`). With all reservoir tiles misplaced, the initial
  potential is `1.75*k²s³` (`four_wrongPotential_le`). This replaced a
  per-transfer charge with one-step look-ahead on the exit side, whose game
  value `2.5*s` was optimal for exits that leave the blank next to the corridor.

A transfer costs at most `s + O(k²)` inefficient moves besides the per-cell
charge: `s` for the entry slide and vertical travel together, plus `s` if it
starts from the last band. Off-diagonal counts never increase, so a reservoir
is the source of at most as many transfers as it initially holds
off-diagonal tiles (`weighted_rowOff_move`). The surcharge is therefore paid at
most `k*s²` times, lower order (`weighted_boardMatrix_le₂`). With the initial
potential, Transport costs `2.75*k²s³ + O(k*s³)`.

**Arrangement.** Two exchange schedules: vertical corridors `V(i,j) ↔ V(j,i)`,
then horizontal corridor rows. Both stage the two families, exchange them with the
row-shift word `θ_m`, and undo the staging by its reverse path, which restores
every tile the staging disturbed. The families may be reordered internally, so
odd family sizes cause no parity problem.

- *Horizontal rows* are cut into slots, one row of one square each, and use the
  paper's shared staging in the top row of the board (`Moves/BulkExchange.lean`).
  An upper slot of band `x`, row `o`, column block `d` holds group `(x,o)` and
  is exchanged with slot `(x,d,o)`, as in the paper. A lower slot holds group
  `(x-1,o)`, which belongs in the band above, so the lower slots are moved by
  two rounds of exchanges: transpose `o` and `d` and reflect the band
  `x ↦ -x`, then reflect it again, `x ↦ k-1-x`; together they move each slot
  up one band (`Arrangement/Horizontal.lean`). There are only `2k³s` such
  tiles, so this is lower order.
- *Vertical corridors* move one family next to the other
  (`Moves/FamilySwap.lean`, `exists_vertical_arrangement_path_near`). Since the
  staging is undone, it only needs to track the two families. The family in the
  lower-numbered column is shifted sideways, one column at a time, by protected
  column shifts (`6m+5` moves per column). The family further down is then
  carried along its own column by a conveyor (`Moves/Conveyor.lean`): the blank
  walks through the segment, shifting it by one, and returns along the
  neighbouring column, `2m+3` moves per row. The two adjacent columns are
  exchanged, and the staging is reversed. A pair costs about
  `2m·(6·Δcol + 2·Δrow)`. Square coordinates of two groups differ by `k/3` on
  average (`3·∑_{a,b<k}|a-b| = k³-k`, `Arrangement/Cost.lean`), so the total is
  `(8/3)·k⁵s² + O(k·s³)` (`sum_vcost_le`), against `24·k⁵s²` for top-row staging.

**Finish.** Squares are not locally solvable in general. As permitted by
Section 3.2 (p. 137), each nonfinal square is solved up to one transposition,
which is paired with a transposition of two buffer tiles in the final square to
give an even permutation (`Finish.lean`). The blank is borrowed from the global
target corner. The final square is solvable because the whole board is
reachable (`Algorithm/ResidualReachability.lean`). The local solver is
abstract (`SolverCostBound`): its cost must hold for every board of side `s`.
The Parberry-style solver gives `5*s³ + O(s²)` moves (`Parberry/Solver.lean`).

The Finish chain carries an inefficiency bound alongside the length bound
(`SolverBound`). The block embedding with borrowed labels is
target-compatible, so it preserves the potential change of every move
(`Path.exists_embedded_efficient`); relabeling two tiles for parity costs at
most twice the distance between their targets
(`Path.inefficientMoves_relabel_swap_le`); and the access conjugation only adds
twice the access length (`Path.exists_conjugated_efficient`).

*Two levels* (`Algorithm/TwoLevel.lean`). The one-level explicit bound is a
local solver with inefficiency `11.73*s^(11/4) + 78252*s^(5/2)` for `s ≥ 12⁴`
(`recursiveSolver`). The suffix after Transport is then charged by inefficiency
(`exists_admissible_solution_of_solver_ineff`): Arrangement by its length plus
its potential increase, which is at most `2s` per non-reservoir cell because
every tile of a sorted board lies in its own square (`arrangement_manhattan`),
and Finish by `k²` local inefficiencies. Arrangement's potential also falls:
each vertical corridor tile of `V(i,j)` starts at least `s*(Δrow+Δcol) - 2s`
from its target and ends within `2s` of it, so the potential drops by about
`(2/3)*k⁵s²`, a quarter of Arrangement's length `(8/3)*k⁵s²`
(`arrangement_manhattan`). Since `s ≥ x³` with `x = n^(1/4)`, the
inner error is `O(x^(41/4)) = O(n^(41/16))`. No induction is needed: the outer
level uses the inner bound only through Finish.

## Arbitrary sides

For a board of side `n ≥ 12⁴`, let `x = n^(1/4)`, take `k = ⌊cx⌋` and
`s = ⌊n/k⌋`, so that `s ≥ k³` (`exists_scaled_dimension`). The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix and the
remaining `k*s × k*s` board by the admissible-board algorithm. The residual
board is reachable and its Manhattan distance equals the original board's
after the prefix (`Algorithm/Residual*.lean`). Then
`k²s³ ≤ n³/k ≤ x¹¹/c + O(x¹⁰)` (since `k > cx - 1`),
`k⁵s² ≤ k³n² ≤ c³x¹¹`, `k*s³ = O(x¹⁰)`, and the prefix costs
`O(n²·k) = O(x¹⁰)`.

**Choice of `k`.** With `k ≈ c*x`, four times the leading inefficiency is
`(A'/c + 52*c³)*x¹¹`, where `A' = 21` with the Parberry Finish (one level) and
`A' = 11` with the recursive Finish (two levels). The minimizer is
`c = (A'/156)^(1/4)`, and at the optimum the constant is
`(4/3)*A^(3/4)*(3P)^(1/4)` for coefficients `A = A'/4` and `P = 13` (one
level) or `P = 12.5` (two levels, where Arrangement is charged less its
potential decrease; the corridor term is then `50*c³`).

| Level | `c` | Constant | Where |
| --- | --- | ---: | --- |
| One (Parberry Finish) | `2/3` | `63/8 + 104/27 ≈ 11.73` | `GeneralSize.exists_solution_explicit` |
| Two (recursive Finish) | `6/11` | `121/24 + 2700/1331 ≈ 7.07` | `TwoLevel.exists_solution_two_level` |

With two levels a unit saved in Transport is worth about `1.92` and a unit saved
in Preparation or Arrangement about `0.14`. The optimal `c ≈ 0.52` would give
`7.05`.

The paper instead rounds `n` down to a fourth power, leaving up to
`4*n^(3/4)` outer layers whose Parberry prefix costs `60*n^(11/4)`. Rounding
to a multiple of `k` removes this term entirely.

## Constant accounting

Leading coefficients of the inefficient moves:

| Source | Coefficient | Where |
| --- | ---: | --- |
| Arrangement (length `8/3` less potential decrease `2/3`, halved) | `k⁵s²` | `Admissible.arrangement_manhattan` |
| Preparation: staging 7.5, vertical spreading 4 | `11.5*k⁵s²` | `Admissible.preparation_phase` |
| Transport: entry and vertical travel 1, per-cell charge 1.75 | `2.75*k²s³` | `Admissible.transport_phase` |
| Finish (recursive solver, charged by inefficiency) | lower order | `TwoLevel.recursiveSolver` |
| **Total**, with `k = ⌊6x/11⌋` | **`7.08*n^(11/4)`** | `TwoLevel.exists_solution_two_level` |

Lower-order terms are collected in one `k*s³` envelope, plus the inner level's
error, and absorbed (as `O(n^(41/16))`) only in `uniformApproximation`.

## Directions for improvement

A broader brainstorm (recursive halving, Preparation redesigns, global structure,
lower bounds and literature), with its simulation scripts, is in
[`research/brainstorm-2026-09/`](research/brainstorm-2026-09/README.md). Its first
candidate, the exit that restores the reservoir (`A` 3.5 → 2.75), is done. The
others are Arrangement as a drain run (lower order) and Preparation by
long-range conveyor families (11.5 → about 4/3), together giving a constant of
about 4.

Coefficients are in inefficiency units. At the balanced `k` the constant
is `(4/3)*A^(3/4)*(3P)^(1/4)` with `A = 2.75` (Transport) and `P = 12.5`
(Preparation 11.5, Arrangement 1), so one unit saved in `A` is worth about
`1.92` and one unit in `P` about `0.14`.

- **Arrangement sideways leg (1 → about 0.33; constant about −0.11).** Families
  move sideways at `6` moves per tile and cell (protected column shifts) but along
  their own axis at `2` (conveyor). Turning a column family into a row costs
  only `O(s)` per tile, which is lower order. So the sideways leg could run as a
  row conveyor, and the leading term would drop from `(8/3)*k⁵s²` to about
  `(4/3)*k⁵s²`. This needs a column-to-row rearrangement lemma that tracks the
  family and is otherwise free, since the staging is reversed anyway.
- **Vertical spreading (4).** Staged columns move sideways into the vertical
  corridors by chunked column translations (`6` per cell). With the conveyor and
  family-swap machinery (`Moves/Conveyor.lean`, `Moves/FamilySwap.lean`),
  moving them along their axis where possible, or converting them to rows,
  should cut this substantially. Alternatively, charge the translations at half
  their length plus displacement, which needs a complete description of their
  effect on the band.
- **Preparation charged by displacement.** Preparation is charged at its full
  length (`ineff ≤ length`). Since `2*ineff = length + ΔM` and `ΔM` is at most
  the net displacement of the tiles (`manhattan_le_of_displacement`), a
  cheaper charge needs the exact effect of the moves. The protected shift `θ_M`
  (length `6M+2`) displaces tiles by `4M-2` in total, so vertical spreading
  would cost `5/3` of its length instead of `2`: `4 → 3.33` (constant about
  `−0.11`). The staged tiles also move toward their targets on average
  (`ΔM ≈ −(1/6)*k⁵s²` for them), which would give about `3` (`−0.17`). Both need
  the full effect of chunked column translations, which is only partly
  recorded now (`exists_chunked_column_translation`).
- **Staging (7.5).** The staging prefix (Parberry column and row solves)
  places exact tiles, although only group membership is needed, and charges
  about `7.5*n` per tile regardless of position. Bulk moves are much cheaper:
  moving `m` tiles one cell along their own row costs about `2m+3`, against
  `5m` for single carries. Exploiting that needs the tiles grouped first, which
  is the open difficulty. A redesign that fills each corridor from nearby tiles
  of the right group, like the Arrangement change, is another option; so is
  tracking Manhattan changes through the `Zhong` placement words, so that carried
  tiles' own moves count as efficient.
- **Transport (2.75, weight 1.92).** Per transfer: entry slide and vertical
  travel together up to `s` (upper and lower corridor rows); per misplaced
  tile, exit and the next horizontal travel `1.75*s` on average over columns.
  Ideas:
  - Horizontal travel is charged `max(o, s-o)`, the worse direction. The count
    run fixes the next direction, and the tile to transport can be any tile of
    the right group in the source reservoir, so a choice by column could lower
    the average, though not in the worst case.
  - A source in the band of `i` could exit vertically into `H_i`
    (brainstorm estimate `2.75 → 2.65`).
  - The exit costs `4` per cell of carry, optimal for walk-and-carry words
    (see above).
- **Finish (lower order at two levels).** Nothing to gain at the leading order.
  The inner level contributes the `O(n^(41/16))` remainder; a third level would
  not change the leading constant.
- **Remainder and thresholds.** The explicit bounds use loose envelopes (`k*s³`
  with coefficients near `3*10⁴`), and `uniformApproximation` absorbs the
  `n^(41/16)` term only at `n ≥ 475686^6`. Tightening these doesn't affect the
  asymptotic constant.
