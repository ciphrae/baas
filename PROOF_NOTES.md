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

## The algorithm on `k⁴ × k⁴` boards

The partition (Section 4.1, pp. 138–139) is defined directly in
`Algorithm/Partition.lean`, including the vertical corridor column
`b_i*k³ + j` exactly as printed. Group membership excludes the blank; the phase
states (`Algorithm/PhaseStates.lean`) record the blank's location separately.

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
(`Transport/Counts.lean`), which terminates after at most `k⁸` transfers, and
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
- Long straight corridor slides cost at most `k³` inefficient moves: after the
  destination interval, every slide moves a tile toward its target
  (`Moves/Corridor.lean`, Fact 3).
- Restoring jumps are charged at half their length plus the jump distance
  (`Path.two_inefficientMoves_le_of_blank_swap`).

A transfer costs at most `9*k³ + O(k²)` inefficient moves: one `k³` each for the
entry slide, horizontal travel and vertical travel, and six for the exit.

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
reachable (`Algorithm/ResidualReachability.lean`). The local solver is a
Parberry-style solver with `5*n³ + O(n²)` moves (`Parberry/Solver.lean`).

## Arbitrary sides

For `k⁴ ≤ n < (k+1)⁴` the outer `d = n - k⁴` rows and columns are solved by the
Parberry prefix and the remaining square by the fourth-power algorithm. The
residual board is reachable and its Manhattan distance equals the original
board's after the prefix (`Algorithm/Residual*.lean`). The prefix's inefficient
moves are bounded by its length, `(15*n² + O(n))*d`, and `d ≤ 4*n^(3/4)`.

## Constant accounting

Leading coefficient of the inefficient moves, in units of `n^(11/4)`:

| Source | Coefficient | Where |
| --- | ---: | --- |
| Size reduction (prefix, charged by length) | 60 | `GeneralSize.outer_layers_budget` |
| Arrangement (length 24, halved) | 12 | `FourthPower.arrangement_bound` |
| Preparation: staging 7.5, vertical spreading 4 | 11.5 | `FourthPower.preparation_phase` |
| Transport | 9 | `FourthPower.transport_phase` |
| Finish (length 5, halved) | 2.5 | `FourthPower.finish_bound` |
| **Total** | **95** | `GeneralSize.exists_solution_explicit` |

Lower-order terms are collected in one `k¹⁰` (respectively `n^(5/2)`) envelope
and absorbed only in `uniformApproximation`.

## Directions for improvement

- **Size reduction (60).** The prefix is charged by its length. Two routes:
  - Generalizing the partition from `k × k` squares of side `k³` to `a × a`
    squares with `a ≈ k` would make `d < k³`, reducing 60 to about 15. Every
    phase is currently stated for `n = k⁴`.
  - Tracking Manhattan changes through the Parberry placements would charge
    each carried tile's own moves as efficient (roughly 60 → 46). This needs
    the effect of the `Zhong` words on all cells, not only the placed tile.
- **Staging (7.5).** The staging prefix places exact tiles, although only group
  membership is needed.
- **Transport exit (6 of 9).** Carrying toward the nearer of the two corridor
  sides would halve most exits. Rightmost squares have only one side, so this
  needs per-reservoir transfer counts from the count run.
- **Vertical spreading (4).** Charging the translations at half their length
  plus displacement needs a complete description of their effect on the band.
