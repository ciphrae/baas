# BAAS: Better Approximation Algorithms for Sliding puzzles

A Lean 4 / mathlib proof that Manhattan distance approximates the optimal
solution length of the `n × n` sliding puzzle within `O(n^(8/3) (log n)^(1/3))`.
This improves the error `O(n^(11/4))` of Proposition 9 in Zhixian Zhong,
*Additive Approximation Algorithms for Sliding Puzzle* (2023), §5.2
(`zhong2023_additive-approximation-sliding-puzzle.pdf`, printed p. 145).

Over the reachable orbit of the standard `n × n` target,

```text
average optimal solution length = (2/3)*n³ + O(n^(8/3) (log n)^(1/3))
God's number                    =       n³ + O(n^(8/3) (log n)^(1/3))
```

These are `SlidingPuzzle.Hub.average_optimal_length` and
`SlidingPuzzle.Hub.gods_number` in
[`SlidingPuzzle/Hub/Main.lean`](SlidingPuzzle/Hub/Main.lean); the corollaries
`…_rpow` give `O(n^α)` for every `α > 8/3`. The boardwise bound behind them is
`Hub.uniform_approximation`: for `n ≥ 4096`, every reachable board has a
solution of length at most `Manhattan + C*n^(8/3)*(log n)^(1/3)`. The constant
is `1,044`, proved by `Hub.uniform_approximation_explicit` (about
4.6 billion times smaller than the original `4,828,800,024,144`).

Here `log` in the error term is the natural logarithm. In explicit form,
for every reachable board and every `n ≥ 4096`,

```text
OPT(B) ≤ Manhattan(B) + 1044·n^(8/3)·(ln n)^(1/3).
```

`Hub.hubConstant_eq` verifies the numerical value. The derivation, including
separate transport and prefix estimates, is documented in
[the Lean proof guide](research/exponent/LEAN_PLAN.md#asymptotics).
The constant is a certified upper bound, not a claim of optimality.

All results are proved outright: no `sorry`, no custom axioms, and no
hypotheses standing in for mathematical steps.

## Building

Lean `v4.33.1` with mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```sh
lake exe cache get
lake build
lake env lean Checks/Axioms.lean   # prints the axioms of the main results
```

All main results depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

| Path | Contents |
| --- | --- |
| `SlidingPuzzle/Basic`, `Target`, `Paths` | Boards as `Cell n ≃ Tile n`, legal moves, paths, reachability, `optimalLength` |
| `SlidingPuzzle/Manhattan`, `Algorithm/Accounting` | Manhattan potential; `length + M(end) = M(start) + 2*inefficientMoves` |
| `SlidingPuzzle/Statistics`, `StatisticalBounds`, `DistanceEstimates`, `OrbitParity` | Orbit mean and maximum, `M ≤ n³`, parity invariant |
| `SlidingPuzzle/Bridge/` | Transfer of reachability and orbit statistics from the `Zhong` word library |
| `SlidingPuzzle/Moves/` | Generic legal-move constructions: jumps, three-cycles, exchanges, embeddings, local solving |
| `SlidingPuzzle/Parberry/` | A Parberry-style solver (`5*n³ + O(n²)`), row/column/layer prefixes |
| `SlidingPuzzle/Algorithm/Partition`, … | Division of a board of side `k*s` into `k × k` squares; region counts |
| `SlidingPuzzle/Algorithm/Finish/`, `Finish` | Solving every square locally once it holds its own tiles (`Partition.FDims`: `8 ≤ s`) |
| `SlidingPuzzle/Algorithm/Residual*` | The board left after solving the outer layers by a prefix |
| `SlidingPuzzle/Hub/Basic`, `Interface`, `Layout` | Hub layout, the abstract state `IState` and its operations, `Rel` to boards |
| `SlidingPuzzle/Hub/Prim*`, `Geom*`, `Op*`, `Simulate` | The operations hop1, hop2, jump on boards, with inefficiency budgets |
| `SlidingPuzzle/Hub/Plan*`, `WalkSnake`, `RoundWalk` | König decomposition of the demand multigraph; the walk of one round |
| `SlidingPuzzle/Hub/Chernoff*`, `InFlight*` | Maclaurin's inequality, subset Chernoff, a good order of the rounds, tiles in flight |
| `SlidingPuzzle/Hub/Run*` | The abstract run: roles, stock identity, validity, cost, leftover misplaced tiles |
| `SlidingPuzzle/Hub/Cleanup`, `FinishGen`, `Transport` | Cleanup by three-cycles and double swaps, Finish, the hub algorithm on side `k*s` |
| `SlidingPuzzle/Hub/Asymp*`, `Main` | Choice of `k ≈ (n/log n)^(1/3)`, general sides, the final theorems |
| `Zhong/` | Word-level puzzle library in the paper's conventions: reachability criterion, orbit statistics, move words |
| `research/exponent/` | Pen-and-paper proof, Lean blueprint, research log and simulations |

## Proof outline

*Statistics* (`Hub/AsympStats`, `Bridge/Statistics`). As in the paper,
Manhattan distance `M` is a lower bound for `OPT`, its orbit mean is
`(2/3)*n³ + O(n²)`, and its maximum over reachable boards is `n³ + O(n²)`. So
it suffices to show `OPT(B) ≤ M(B) + C*n^(8/3)*(log n)^(1/3)` for every
reachable board, i.e. a solution with that many inefficient moves.

*Why `11/4` is not optimal.* Zhong divides the board into `k²` squares with
reservoirs and corridors. Transport costs `O(n³/k)`, and the `k³n` corridor
tiles, each placed at cost `O(n)`, cost `O(k³n²)`; balancing gives
`k = n^(1/4)` and `n^(11/4)`. Corridors pure in the full class need `k³n`
cells, since each of `k²` classes must reach `k²` squares. The hub scheme uses
`O(k²n)` corridor cells, homogeneous in one coordinate only: row corridor
`R(b,c)` carries tiles by target block column `c`, column corridor `C(c,a)`
carries class `(a,c)`. A tile travels `(b,J) → (b,c) → (a,c)`; at the corner
it drops into the reservoir of the *hub* square `(b,c)`, which serves
column-`c` classes to the column corridors from its stock. Balancing `n³/k`
against `k²n²·log n` gives `k ≈ (n/log n)^(1/3)`.

* *Plan* (`Hub/Plan`, `RoundWalk`). The demand multigraph of the reservoirs,
  padded with dummy edges and loops, is regular and splits into perfect
  matchings (Hall/König). In each round every square sends one tile and
  receives one; the blank follows the tiles backwards along the cycles, and
  cycles are started in snake order so that relocations telescope.
* *Operations* (`Hub/Simulate`). hop1 (row, into a hub), hop2 (column, out of
  a hub) and a straight jump (relocation or bypass), built from reservoir
  walks, corridor walks, jumps and three-cycles in local boxes, each within
  `O(s + k²)` inefficient moves plus one per junk corridor tile it moves.
* *Stock* (`Hub/Run`). A hub's stock of a class equals the tiles that dropped
  in, minus those of that class inserted and still in flight, plus bypasses. A
  bypass (an `O(n)` jump from a reserve) happens only at stock zero, so
  bypasses are bounded by the in-flight maxima.
* *In flight* (`Hub/InFlight`). Row halves are delay lines. Executing the
  rounds in a good order, which exists by a Chernoff bound for sampling
  without replacement (Maclaurin's inequality), keeps the tiles in flight at
  `O(n log n)` per hub.
* *Cleanup and Finish* (`Hub/Cleanup`, `FinishGen`). The `O(k²n log n)` tiles
  left outside their squares are fixed at least two at a time, by a three-cycle
  or a double swap at `O(n)` each; each square is then solved locally,
  `k²·O(s³) = O(n³/k)`.
* *Arbitrary sides* (`Hub/AsympBound`). With `s = ⌊n/k⌋`, the outer
  `n - k*s < k` layers are solved by a Parberry prefix, which is lower order.

There is no Preparation phase: corridors start with arbitrary tiles, which
cost `O(n)` each until they drop out.

[`PROOF_NOTES.md`](PROOF_NOTES.md) relates the shared parts to the paper and
records where the formalization departs from it. The pen-and-paper proof of
the bound is [`research/exponent/PROOF.md`](research/exponent/PROOF.md), and
[`research/exponent/LEAN_PLAN.md`](research/exponent/LEAN_PLAN.md) records how
its Lean proof is organized and where it departs from the paper proof.

## Prior work

Zhixian Zhong, *Additive Approximation Algorithms for Sliding Puzzle* (2023),
included as `zhong2023_additive-approximation-sliding-puzzle.pdf`. Its
Proposition 9 gives the same statements with error `O(n^(11/4))`. This project
follows its conventions, its reduction to a boardwise bound, and its division
of the board into squares with reservoirs and corridors and a local Finish;
the transport through hub squares is new.
