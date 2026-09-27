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
bound. Instead, for `n ≥ 2^39` take `k = 2m` with
`64·m³(log₂ n + 1) ≤ n < 64(m+1)³(log₂ n + 1)` and `s = ⌊n/k⌋`. The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix
(`Parberry/Prefix.lean`, `O(n²·k)`), and the remaining `k*s × k*s` board by the
hub algorithm. The residual board is reachable and its Manhattan distance
equals the original board's after the prefix (`Algorithm/Residual*.lean`,
`Hub/AsympBound.lean`). The existing cubic solver handles
`4096 ≤ n ≤ 2^39`, so the final theorem still starts at `4096`.

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
  tiles left outside their squares at the end are exchanged home by double
  swaps (`Hub/Cleanup.lean`, `O(n)` each).
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

The boardwise constant is now `19,319` for `n ≥ 4096`, down from
`20,816` before combined accounting and the fractional in-flight budget,
`27,508` before retaining size-dependent budgets,
`27,607` before the transport-arithmetic refinement, `27,609` before the
prefix refinement, `849,303` in an earlier version and
`4,828,800,024,144` originally. The threshold and asymptotic exponent
are unchanged. The certified estimates are:

- Staging and rotations: the boundary placement costs `8n + 98m + 12`
  on an `n × m` board, obtained by retaining the actual raising and strip
  costs. For three-tile staging, the second and third placements use the
  existing sharp Parberry routine. The resulting three-cycle costs `254n`
  moves and a double swap costs `508n`.
- Operations: hops and jumps use linear coefficient `288`; a two-jump
  relocation uses `576`. The quadratic hop2 allowance remains `30k²`.
- Union bound: the number of window events is at most `n⁴`, using the
  existing room condition. Thus `λ = 4L` suffices, with `L = log₂ n + 1`.
  The capacity condition becomes `25kL ≤ s`, since `6kλ ≤ s-k`.
- In-flight budget: `Rhub n = ⌊(28nL + 22n)/5⌋ + 1`. The sum is bounded by
  `4n(1+(7/5)L) + 8k + 8k²L`, using `ln(kΔ) ≤ (7/5)L`.
  Capacity gives `8k²L ≤ 8n/25` and `s ≥ 500` gives `8k ≤ 8n/500`.
  The old `7nL` estimate remains available as a compatibility bound.
- Capacity also implies `L ≥ 10`, `s ≥ 500`, and `n ≥ 1000`.
  Retaining these lower bounds avoids charging small terms as full
  leading-order contributions.
- Transport: `2883X + 2148Y` on the large grid, where `X = n²s`,
  `Y = k²n²L`; the generic bound `4032X + 3592Y` remains available.
  The raw run budgets retain their dependence on `k`, `n`, and `L`.
  For `L ≥ 39`, misplaced region tiles are bounded by `22k²nL`,
  improving the generic `24k²nL`.
- Cleanup: `508n(misplaced + 2n + 1)`.
- Whole hub algorithm on the large grid: `2886.937X + 10772.414Y`, including
  local Finish. The proof carries integer numerators over `1000` through
  `AsympAccounting.lean`, using `k ≥ 1196`, `L ≥ 39`, and capacity.
  The older bounds `2893X + 13351Y` and `4042X + 15888Y` remain available.
- Grid for `n ≥ 2^39`: `k = 2m`, with `64m³L ≤ n < 64(m+1)³L`.
  The threshold ensures `m ≥ 598`. Keeping the ratio `(m+1)/m ≤ 599/598`
  gives `(299X)³ ≤ 599³n⁸L`; the corridor bound is `(4Y)³ ≤ n⁸L`.
  The prefix satisfies `(1000Z)³ ≤ n⁸L` for the large-board range.
- Natural logarithms on this range: `L ≤ 1.479688 ln n`.
  The rational factor `1.139524` has cube at least `1.479688`.
- Initial range: for `4096 ≤ n ≤ 2^39`, the existing Parberry solver
  costs at most `6n³ ≤ 18000·hubError n`, splitting at `2^36` and using
  `ln n ≥ 24` above that split. Thus this branch fits the same
  final coefficient without adding its cost to the hub branch.

Consequently the hub branch's real coefficient is
`2·1.139524·((599/299)·2886.937 + 10772.414/4 + 1/1000)`, approximately
`19318.655326`. Rounding upward gives `C = 19,319`, which also covers
`18000` from the initial range.
`Hub.uniform_approximation_explicit` exposes the numerical bound directly.
This is a certified upper bound, not a claim of optimality.

## Remaining structural improvements

The inexpensive accounting and routine-reuse improvements have been carried
through to the final bound. The prefix term is now nearly negligible; the
main cost is now the relocation/local term. Substantial further reductions
would need a more precise relocation analysis, a more tightly coupled treatment
of the grid and run costs, or new staging/cleanup paths. These would reorganize
proofs beyond this pass. Removing the logarithm would require a stronger
in-flight argument; the simulations in `research/exponent/` suggest that
possibility but do not prove it.
