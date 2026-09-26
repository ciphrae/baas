# Sliding puzzle: Proposition 9 in Lean, and a better exponent

A Lean 4 / mathlib formalization of Proposition 9 of Zhixian Zhong,
*Additive Approximation Algorithms for Sliding Puzzle* (2023), §5.2
(`zhong2023_additive-approximation-sliding-puzzle.pdf`, printed p. 145), and
of a strictly better error term obtained by a new transport scheme.

Over the reachable orbit of the standard `n × n` target,

```text
average optimal solution length = (2/3)*n³ + O(n^(8/3) (log n)^(1/3))
God's number                    =       n³ + O(n^(8/3) (log n)^(1/3))
```

These are `SlidingPuzzle.Hub.average_optimal_length` and
`SlidingPuzzle.Hub.gods_number` in
[`SlidingPuzzle/Hub/Main.lean`](SlidingPuzzle/Hub/Main.lean); the corollaries
`…_rpow` give `O(n^α)` for every `α > 8/3`. Zhong's exponent is `11/4`. The
boardwise bound behind them is `Hub.uniform_approximation`: for `n ≥ 4096`,
every reachable board has a solution of length at most
`Manhattan + C*n^(8/3)*(log n)^(1/3)` (the constant is explicit but huge; it
was never optimized).

Zhong's own result is formalized too, with an optimized constant:

```text
average optimal solution length = (2/3)*n³ + O(n^(11/4))
God's number                    =       n³ + O(n^(11/4))
```

(`SlidingPuzzle.average_optimal_length`, `SlidingPuzzle.gods_number` and their
conjunction `SlidingPuzzle.proposition9` in
[`SlidingPuzzle/Main.lean`](SlidingPuzzle/Main.lean)). Its boardwise bound
(`Algorithm.exists_solution_two_level`): for every `n ≥ 36⁴`, every reachable
board has a legal solution with at most

```text
7.08*n^(11/4) + 237843*n^(41/16)
```

inefficient moves, i.e. of length at most `Manhattan + 14.15*n^(11/4) + 475686*n^(41/16)`.
The one-level algorithm alone gives `11.73*n^(11/4) + 78252*n^(5/2)` for
`n ≥ 12⁴` (`Algorithm.exists_solution_explicit`). Since `n^(8/3)(log n)^(1/3)`
beats `n^(11/4)` only for astronomically large `n` with the present constants,
the two developments are complementary: one has the better exponent, the other
the usable constant.

All results are proved outright: no `sorry`, no custom axioms, and no
hypotheses standing in for mathematical steps.

## Building

Lean `v4.33.1` with mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```sh
lake exe cache get
lake build
lake env lean Checks/Axioms.lean   # prints the axioms of the main results
```

All main results, for both exponents, depend only on `propext`,
`Classical.choice` and `Quot.sound`.

## Layout

| Path | Contents |
| --- | --- |
| `SlidingPuzzle/Basic`, `Target`, `Paths` | Boards as `Cell n ≃ Tile n`, legal moves, paths, reachability, `optimalLength` |
| `SlidingPuzzle/Manhattan`, `Algorithm/Accounting` | Manhattan potential; `length + M(end) = M(start) + 2*inefficientMoves` |
| `SlidingPuzzle/Statistics`, `StatisticalBounds`, `DistanceEstimates`, `OrbitParity` | Orbit mean and maximum, `M ≤ n³`, parity invariant |
| `SlidingPuzzle/Bridge/` | Transfer of reachability and orbit statistics from the `Zhong` library |
| `SlidingPuzzle/Proposition9`, `Main` | Proposition 9 from a boardwise bound; the final `11/4` theorems |
| `SlidingPuzzle/Moves/` | Generic legal-move constructions: jumps, carries, translations, exchanges, local solving |
| `SlidingPuzzle/Parberry/` | A Parberry-style solver (`5*n³ + O(n²)`), row/column/layer prefixes |
| `SlidingPuzzle/Algorithm/Partition`, … | The partition of Section 4.1 (generalized to squares of side `s ≥ k³`) and its counts |
| `SlidingPuzzle/Algorithm/Preparation/`, `Preparation` | Phase I |
| `SlidingPuzzle/Algorithm/Transport/`, `Transport` | Phase II (Algorithm 4) |
| `SlidingPuzzle/Algorithm/Arrangement/`, `Arrangement` | Phase III |
| `SlidingPuzzle/Algorithm/Finish/`, `Finish` | Phase IV (needs only `Partition.FDims`: `8 ≤ s`, shared with the hub algorithm) |
| `SlidingPuzzle/Algorithm/Admissible` | The four phases composed on boards of side `k*s`, `s ≥ k³` |
| `SlidingPuzzle/Algorithm/GeneralSize` | Reduction of arbitrary sides to admissible ones |
| `SlidingPuzzle/Algorithm/TwoLevel` | The one-level bound as the Finish solver; the final boardwise bound |
| `SlidingPuzzle/Hub/Basic`, `Interface`, `Layout` | Hub layout, the abstract state `IState` and its operations, `Rel` to boards |
| `SlidingPuzzle/Hub/Prim*`, `Geom*`, `Op*`, `Simulate` | The operations hop1, hop2, jump on boards, with inefficiency budgets |
| `SlidingPuzzle/Hub/Plan*`, `WalkSnake`, `RoundWalk` | König decomposition of the demand multigraph; the walk of one round |
| `SlidingPuzzle/Hub/Chernoff*`, `InFlight*` | Maclaurin's inequality, subset Chernoff, a good order of the rounds, tiles in flight |
| `SlidingPuzzle/Hub/Run*` | The abstract run: roles, stock identity, validity, cost, leftover misplaced tiles |
| `SlidingPuzzle/Hub/Cleanup`, `FinishGen`, `Transport` | Cleanup by double swaps, Finish, the hub algorithm on side `k*s` |
| `SlidingPuzzle/Hub/Asymp*`, `Main` | Choice of `k ≈ (n/log n)^(1/3)`, general sides, the final `8/3` theorems |
| `Zhong/` | Word-level puzzle library from an earlier formalization attempt: reachability criterion, orbit statistics, move words |

## Proof outline: Zhong's algorithm, `n^(11/4)`

*Statistics* (`Proposition9`, `Bridge/Statistics`). Manhattan distance `M` is a
lower bound for `OPT`, its orbit mean is `(2/3)*n³ + O(n²)`, and its maximum over
reachable boards is `n³ + O(n²)`. So it suffices to show
`OPT(B) ≤ M(B) + C*n^(11/4)` for every reachable board, i.e. a solution with
`O(n^(11/4))` inefficient moves.

*Admissible boards* (`Algorithm/Admissible`). The paper divides a board of side
`n = k⁴` into `k²` squares of side `k³`, one per target group, each with
horizontal and vertical corridors and a reservoir. The construction only needs
squares of side `s ≥ k³` (`Partition.Dims`), so it applies to every board of
side `n = k*s`. The phases cost two different monomials, `k²s³ = n³/k` and
`k⁵s² = k³n²`, which agree only when `s = k³`. Four times the inefficient moves
are bounded by `21*k²s³ + 52*k⁵s² + 78128*k*s³`:

| Phase | What it does | Leading inefficiency |
| --- | --- | ---: |
| Preparation | Stage corridor tiles with a column prefix, spread them into the corridors | `11.5*k⁵s²` |
| Transport | Algorithm 4: move tiles between reservoirs through the corridors, at most `n²` transfers, each entering the corridor row above or below its reservoir and leaving through the side of the source reservoir nearer the tile, by a three-row carry that the blank undoes on its way back, so that misplaced tiles never change column and are charged once each by their column | `2.75*k²s³` |
| Arrangement | Exchange corridor families so every tile is in its own square, moving one family next to the other (length `8/3`, rounded up to 3 and halved; at two levels, less the potential decrease `2/3`, halved) | `1.5*k⁵s²`, or `k⁵s²` |
| Finish | Solve each square with a local solver: Parberry (length `5s³`, halved), or the one-level algorithm (inefficiency `O(s^(11/4))`) | `2.5*k²s³`, or lower order |

*Arbitrary sides* (`Algorithm/GeneralSize`). Take `k = ⌊(2/3)*n^(1/4)⌋` and
`s = ⌊n/k⌋ ≥ k³`. Only the outer `n - k*s < k` layers need the Parberry prefix,
which is lower order. With `k ≈ c*n^(1/4)` the leading inefficiency is
`(5.25/c + 13*c³)*n^(11/4)`; `c = 2/3` is close to the minimizer and gives
`11.73` (the paper's `c = 1` gives `18.25`).

*Two levels* (`Algorithm/TwoLevel`). The one-level algorithm is itself a local
solver for Finish, with inefficiency `O(s^(11/4))`. Charging Arrangement and
Finish by inefficiency rather than by half their length, Finish becomes lower
order, and Arrangement costs its length less the potential decrease: it moves
every vertical corridor tile into its own square, about `(2/3)*k⁵s²` in total,
and leaves the reservoirs alone. Then `c = 6/11` gives
`(2.75/c + 12.5*c³)*n^(11/4) ≤ 7.08*n^(11/4)`. The inner level's error
adds a term `O(n^(41/16))`, still of lower order.

## Proof outline: hub transport, `n^(8/3) (log n)^(1/3)`

`11/4` is the balance of Transport, `O(n³/k)`, against Zhong's `k³n` corridor
tiles, each placed at cost `O(n)`. Class-pure corridors reaching all `k²`
squares for all `k²` classes need `k³n` cells. The hub scheme uses `O(k²n)`
corridor cells, homogeneous in one coordinate only: row corridor `R(b,c)`
carries tiles by target block column `c`, column corridor `C(c,a)` carries
class `(a,c)`. A tile travels `(b,J) → (b,c) → (a,c)`; at the corner it drops
into the reservoir of the *hub* square `(b,c)`, which serves column-`c`
classes to the column corridors from its stock. Balancing `n³/k` against
`k²n²·log n` gives `k ≈ (n/log n)^(1/3)`.

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
  left outside their squares are fixed by double swaps at `O(n)` each; each
  square is then solved locally, `k²·O(s³) = O(n³/k)`.

There is no Preparation: corridors start with arbitrary tiles, which cost
`O(n)` each until they drop out.

[`PROOF_NOTES.md`](PROOF_NOTES.md) relates each step to the paper, records where
the formalization departs from the printed argument, and lists directions for
lowering the constant. The pen-and-paper proof of the hub bound is
[`research/exponent/PROOF.md`](research/exponent/PROOF.md), and
[`research/exponent/LEAN_PLAN.md`](research/exponent/LEAN_PLAN.md) records how
its Lean proof is organized and where it departs from the paper proof.
