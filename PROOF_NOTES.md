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

A transfer costs at most `6*s + O(k²)` inefficient moves: one `s` each for the
entry slide, horizontal travel and vertical travel, and three for the exit, plus
`3*s` if the source lies in the rightmost column. Off-diagonal counts never
increase, so a reservoir is the source of at most as many transfers as it
initially holds off-diagonal tiles (`weighted_rowOff_move`). The rightmost
column's surcharge is therefore at most `k*s²*3s`, lower order
(`weighted_boardMatrix_le`).

**Arrangement.** The two exchange schedules (vertical corridors `V(i,j) ↔ V(j,i)`,
then horizontal slices) use the paper's shared staging: both families are staged
in the top row, exchanged by the row-shift word `θ_m`, and unstaged by the reverse
path (`Moves/BulkExchange.lean`). The families may be reordered internally, so
odd family sizes cause no parity problem.

**Finish.** Squares are not locally solvable in general. As permitted by
Section 3.2 (p. 137), each nonfinal square is solved up to one transposition,
which is paired with a transposition of two buffer tiles in the final square to
give an even permutation (`Finish.lean`). The blank is borrowed from the global
target corner. The final square is solvable because the whole board is
reachable (`Algorithm/ResidualReachability.lean`). The local solver is
abstract (`SolverCostBound`): its cost must hold for every board of side `s`.
The Parberry-style solver gives `5*s³ + O(s²)` moves (`Parberry/Solver.lean`).

*Two levels* (`Algorithm/TwoLevel.lean`). Every board of side `s` has `M ≤ s³`
(`manhattan_le_cube`), so the one-level explicit bound is a local solver with
cost `s³ + 38.49*s^(11/4) + 125330*s^(5/2)` for `s ≥ 10000` (`recursiveCost`).
Finish then costs `k²s³ + O(k²s^(11/4))` in length. Since `s ≥ x³` with
`x = n^(1/4)`, the inner error is `O(x^(41/4)) = O(n^(41/16))`. No induction is
needed: the outer level uses the inner bound only through Finish.

## Arbitrary sides

For a board of side `n ≥ 10000`, let `x = n^(1/4)`, take `k = ⌊3x/5⌋` (one level) and
`s = ⌊n/k⌋`, so that `s ≥ k³` (`exists_scaled_dimension`). The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix and the
remaining `k*s × k*s` board by the admissible-board algorithm. The residual
board is reachable and its Manhattan distance equals the original board's
after the prefix (`Algorithm/Residual*.lean`). Then
`k²s³ ≤ n³/k ≤ (5/3)x¹¹ + 4x¹⁰` (since `k > 3x/5 - 1`),
`k⁵s² ≤ k³n² ≤ (27/125)x¹¹`, `k*s³ ≤ 4x¹⁰`, and the prefix costs
`O(n²·k) = O(x¹⁰)`.

**Choice of `k`.** With `k ≈ c*x`, twice the leading inefficiency is
`(A'/c + 47*c³)*x¹¹`, where `A' = 17` with the Parberry Finish (one level) and
`A' = 13` with the recursive Finish (two levels). The minimizer is
`c = (A'/141)^(1/4)`, and at the optimum the constant is
`(4/3)*A^(3/4)*(3P)^(1/4)` for halved coefficients `A = A'/2` and `P = 23.5`.

| Level | `c` | Constant | Where |
| --- | --- | ---: | --- |
| One (Parberry Finish) | `3/5` | `85/6 + 1269/250 ≈ 19.25` | `GeneralSize.exists_solution_explicit` |
| Two (recursive Finish) | `11/20` | `130/11 + 62557/16000 ≈ 15.73` | `TwoLevel.exists_solution_two_level` |

With two levels a unit saved in Transport is worth about `1.82` and a unit saved
in Preparation or Arrangement about `0.17`.

The paper instead rounds `n` down to a fourth power, leaving up to
`4*n^(3/4)` outer layers whose Parberry prefix costs `60*n^(11/4)`. Rounding
to a multiple of `k` removes this term entirely.

## Constant accounting

Leading coefficients of the inefficient moves:

| Source | Coefficient | Where |
| --- | ---: | --- |
| Arrangement (length 24, halved) | `12*k⁵s²` | `Admissible.arrangement_bound` |
| Preparation: staging 7.5, vertical spreading 4 | `11.5*k⁵s²` | `Admissible.preparation_phase` |
| Transport | `6*k²s³` | `Admissible.transport_phase` |
| Finish (length `s³` per square with the recursive solver, halved) | `0.5*k²s³` | `TwoLevel.recursiveSolverCost` |
| **Total**, with `k = ⌊11x/20⌋` | **`15.73*n^(11/4)`** | `TwoLevel.exists_solution_two_level` |

Lower-order terms are collected in one `k*s³` envelope, plus the inner level's
error, and absorbed (as `O(n^(41/16))`) only in `uniformApproximation`.

## Directions for improvement

Given the weights above, Transport is the phase worth attacking.

- **Arrangement (12, weight 0.17).** Families are staged at the top row of the board, so each
  exchanged tile travels up to `n` twice. Staging nearer to the squares involved,
  or accounting for the tiles' progress toward their targets, would reduce it.
- **Staging (7.5, weight 0.17).** The staging prefix places exact tiles, although only group
  membership is needed.
- **Transport (6).** The entry slide, horizontal travel, vertical travel and
  exit each cost up to `s` per transfer (weight 1.82).
- **Vertical spreading (4, weight 0.17).** Charging the translations at half their length
  plus displacement needs a complete description of their effect on the band.
- **Parberry placements.** Tracking Manhattan changes through the `Zhong` words
  would let carried tiles' own moves count as efficient in staging.
