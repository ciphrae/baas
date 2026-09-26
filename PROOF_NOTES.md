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
bound. Instead, for `n ≥ 4096` take `k = 2m` with
`256·m³(log₂ n + 1) ≤ n < 256(m+1)³(log₂ n + 1)` and `s = ⌊n/k⌋`. The outer
`d = n - k*s < k` rows and columns are solved by the Parberry prefix
(`Parberry/Prefix.lean`, `O(n²·k)`), and the remaining `k*s × k*s` board by the
hub algorithm. The residual board is reachable and its Manhattan distance
equals the original board's after the prefix (`Algorithm/Residual*.lean`,
`Hub/AsympBound.lean`).

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

No constants were optimized; the boardwise constant is about `5·10¹²`, so the
bound beats `C*n^(11/4)` for the paper's constant only for astronomically
large `n`.

## Directions for improvement

Nothing has been optimized. The leading terms are `n³/k` (hops, Finish) and
`k²n² log n` (bypasses, cleanup), and the logarithm comes only from the
in-flight bound: simulations in `research/exponent/` show no visible
logarithm, so `O(n^(8/3))` may be provable with a sharper in-flight argument.
The constants of the primitives (`3022*m` per three-cycle, `25*(dist+1)` per
jump, `6044·n` per double swap) and the envelopes in `Hub/RunBounds.lean` and
`Hub/AsympBound.lean` are loose.
