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

**Generalization.** The paper uses `n = k⁴` and squares of side `k³`. Nothing
in the construction needs the square side to be exactly `k³`: it needs room
for `k` horizontal corridor rows and `k²` vertical corridor columns per square,
and for the compressed staging area of width `k³`. So the partition is stated
for squares of side `s = side n k = n/k` subject to `Dims n k`: `2 ≤ k`,
`k³ ≤ s` and `k*s = n`. Every phase is proved in this generality, with costs
of the form `A*k²s³ + C*k⁵s² + O(k*s³)`. Both monomials are the paper's `k¹¹`
when `s = k³`, but they scale differently in `k` for fixed `n`: `k²s³ = n³/k`
(Transport, Finish) and `k⁵s² = k³n²` (Preparation, Arrangement, which move
the `k³n` corridor tiles a distance of order `n`).

**Preparation.** Every group's corridor quota is staged in the first `k³`
columns and the first `k²` rows (`Preparation/Staging.lean`), together with one
spare tile per nonfinal group in row `k²`. A mixed prefix solves the first `k³`
columns (transposed row solver) and then `k²+1` rows (`Parberry/MixedPrefix.lean`),
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
  matter. The blank first slides to the top of its reservoir
  (`Transport/ReservoirSlide.lean`), so the entry jump crosses only the corridor
  rows. At the exit it walks to the source tile and carries it to the corridor
  side of the reservoir with five-move carries (`Transport/Carry.lean`), then
  exchanges it into the corridor with short jumps.
- Long straight corridor slides cost at most `s` inefficient moves: after the
  destination interval, every slide moves a tile toward its target
  (`Moves/Corridor.lean`, Fact 3).
- Restoring jumps are charged at half their length plus the jump distance
  (`Path.two_inefficientMoves_le_of_blank_swap`).
- *Nearer side:* the source tile is carried to whichever side of its reservoir
  is nearer: the left, through the square's own vertical corridor `V(j,i)`, or
  the right, through the corridor `V(j',i)` of the square `j'` to its right
  (`Transport/Step.lean`). Both corridors hold group `i`, and the exit is one
  orientation-free core (`exists_transport_exit_core`) instantiated twice.
  Squares in the rightmost column have only the left side.

- *Exit charged by potential:* the walk to the source tile and the carries back
  form one word of length `6d` (`Moves/ExitCarry.lean`), but its tiles move
  little in net: the potential rises by at most `4d+2`, so at most `5d+1` of its
  moves are inefficient. The proof is an induction on `d` that follows the
  first walked tile, whose displacement partly cancels in the next carry.

- *Look-ahead:* horizontal travel is inefficient only inside the square the
  blank starts from, so it costs the distance from the blank's column to that
  square's edge in the direction of travel (`exists_horizontal_transport_slide_dir'`).
  The blank's column is where the previous exit left it, next to the left or
  right edge. The count run is deterministic (`Chooses.unique`), so when a
  transfer exits, the next source is already known. The exit side minimises
  `10·d_side + 2·horizontal + Ψ_next`, where the potential `Ψ`
  (`transferPotential`) is twice the distance to the edge facing the next
  source, or `s` if the next source is in the same column of squares. Summing
  the two options gives `cost_L + cost_R ≤ 12s + 2Ψ_now + O(k²)` in every case,
  so the cheaper one satisfies `2·(exit + horizontal) + Ψ_next ≤ 6s + Ψ_now + O(k²)`
  (`transportStepBoundAmortized_of_vertical_bound`). The potentials telescope
  along the run (`exists_path_of_count_run_amortized`). A small game analysis
  shows `3s` per transfer is optimal for one-step look-ahead, against `3.5s`
  without it.

A transfer costs at most `5*s + O(k²)` inefficient moves on average: one `s`
each for the entry slide and vertical travel, `3*s` for exit and horizontal
travel together, plus `4*s` if the source lies in the rightmost column. Off-diagonal counts never
increase, so a reservoir is the source of at most as many transfers as it
initially holds off-diagonal tiles (`weighted_rowOff_move`). The rightmost
column's surcharge is therefore at most `k*s²*3s`, lower order
(`weighted_boardMatrix_le`).

**Arrangement.** Two exchange schedules: vertical corridors `V(i,j) ↔ V(j,i)`,
then horizontal slices. Both stage the two families, exchange them with the
row-shift word `θ_m`, and undo the staging by its reverse path, which restores
every tile the staging disturbed. The families may be reordered internally, so
odd family sizes cause no parity problem.

- *Horizontal slices* use the paper's shared staging in the top row of the board
  (`Moves/BulkExchange.lean`). There are only `k³s` such tiles, so this is lower
  order.
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
local solver with inefficiency `18.38*s^(11/4) + 62663*s^(5/2)` for `s ≥ 12⁴`
(`recursiveSolver`). The suffix after Transport is then charged by inefficiency
(`exists_admissible_solution_of_solver_ineff`): Arrangement by its length plus
its potential increase, which is at most `2s` per non-reservoir cell because
every tile of a sorted board lies in its own square (`arrangement_manhattan`),
and Finish by `k²` local inefficiencies. Since `s ≥ x³` with `x = n^(1/4)`, the
inner error is `O(x^(41/4)) = O(n^(41/16))`. No induction is needed: the outer
level uses the inner bound only through Finish.

## Arbitrary sides

For a board of side `n ≥ 12⁴`, let `x = n^(1/4)`, take `k = ⌊7x/12⌋` (one level) and
`s = ⌊n/k⌋`, so that `s ≥ k³` (`exists_scaled_dimension`). The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix and the
remaining `k*s × k*s` board by the admissible-board algorithm. The residual
board is reachable and its Manhattan distance equals the original board's
after the prefix (`Algorithm/Residual*.lean`). Then
`k²s³ ≤ n³/k ≤ (12/7)x¹¹ + 4x¹⁰` (since `k > 7x/12 - 1`),
`k⁵s² ≤ k³n² ≤ (343/1728)x¹¹`, `k*s³ ≤ 4x¹⁰`, and the prefix costs
`O(n²·k) = O(x¹⁰)`.

**Choice of `k`.** With `k ≈ c*x`, twice the leading inefficiency is
`(A'/c + 26*c³)*x¹¹`, where `A' = 15` with the Parberry Finish (one level) and
`A' = 10` with the recursive Finish (two levels). The minimizer is
`c = (A'/78)^(1/4)`, and at the optimum the constant is
`(4/3)*A^(3/4)*(3P)^(1/4)` for halved coefficients `A = A'/2` and `P = 13`.

| Level | `c` | Constant | Where |
| --- | --- | ---: | --- |
| One (Parberry Finish) | `2/3` | `45/4 + 104/27 ≈ 15.11` | `GeneralSize.exists_solution_explicit` |
| Two (recursive Finish) | `3/5` | `25/3 + 351/125 ≈ 11.14` | `TwoLevel.exists_solution_two_level` |

With two levels a unit saved in Transport is worth about `1.67` and a unit saved
in Preparation or Arrangement about `0.21`.

The paper instead rounds `n` down to a fourth power, leaving up to
`4*n^(3/4)` outer layers whose Parberry prefix costs `60*n^(11/4)`. Rounding
to a multiple of `k` removes this term entirely.

## Constant accounting

Leading coefficients of the inefficient moves:

| Source | Coefficient | Where |
| --- | ---: | --- |
| Arrangement (length 3, halved) | `1.5*k⁵s²` | `Admissible.arrangement_bound` |
| Preparation: staging 7.5, vertical spreading 4 | `11.5*k⁵s²` | `Admissible.preparation_phase` |
| Transport | `5*k²s³` | `Admissible.transport_phase` |
| Finish (recursive solver, charged by inefficiency) | lower order | `TwoLevel.recursiveSolver` |
| **Total**, with `k = ⌊3x/5⌋` | **`11.145*n^(11/4)`** | `TwoLevel.exists_solution_two_level` |

Lower-order terms are collected in one `k*s³` envelope, plus the inner level's
error, and absorbed (as `O(n^(41/16))`) only in `uniformApproximation`.

## Directions for improvement

- **Transport (5, weight 1.67).** The entry slide and vertical travel each cost
  up to `s` per transfer, exit and horizontal travel `3*s` together.
- **Staging (7.5, weight 0.21).** The staging prefix places exact tiles, although only group
  membership is needed. Moving rows of tiles along their own row costs about 2
  moves per tile and cell, against 5–6 for single carries, which staging does not
  exploit.
- **Vertical spreading (4, weight 0.21).** Charging the translations at half their length
  plus displacement needs a complete description of their effect on the band.
- **Arrangement sideways moves (1.5, weight 0.21).** Families move sideways at
  `6` per cell and along their axis at `2`; turning a column into a row for the
  sideways leg costs only `O(s)` per tile, so the leading term could drop to
  about `(4/3)*k⁵s²`.
- **Parberry placements.** Tracking Manhattan changes through the `Zhong` words
  would let carried tiles' own moves count as efficient in staging.
