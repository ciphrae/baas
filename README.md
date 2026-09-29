# BAAS: Better Approximation Algorithms for Sliding puzzles

A Lean 4 / mathlib proof that Manhattan distance approximates the optimal
solution length of the `n × n` sliding puzzle within `O(n^(5/2) (ln n)^(3/2))`.
This improves the error `O(n^(11/4))` of Proposition 9 in Zhixian Zhong,
*Additive Approximation Algorithms for Sliding Puzzle* (2023), §5.2
(`zhong2023_additive-approximation-sliding-puzzle.pdf`, printed p. 145).

For every reachable board `B` of side `n ≥ 8·256³ ≈ 1.3·10⁸`
(`SlidingPuzzle.Tree.tree_log_approximation_explicit`,
[`Tree/MixLog.lean`](SlidingPuzzle/Tree/MixLog.lean)),

```text
OPT(B) ≤ Manhattan(B) + 3200·n^(5/2)·(ln n)^(3/2).
```

Hence, over the reachable orbit of the standard `n × n` target,

```text
average optimal solution length = (2/3)*n³ + O(n^(5/2) (ln n)^(3/2))
God's number                    =       n³ + O(n^(5/2) (ln n)^(3/2))
```

(`Tree.tree_log_average_optimal_length`, `Tree.tree_log_gods_number` in
[`Tree/Stats.lean`](SlidingPuzzle/Tree/Stats.lean)). The constant `3200` holds
uniformly from `1.3·10⁸` on; the bound it is derived from tends to about
`125·n^(5/2)·(ln n)^(3/2)` as `n` grows.

The algorithm routes tiles through a hierarchy of `h` lane levels. At a fixed
depth `h ≥ 1` (`Tree.tree_uniform_approximation_explicit`,
[`Tree/MixGrid.lean`](SlidingPuzzle/Tree/MixGrid.lean)), for every reachable
board with `n ≥ 8h·256^(2h+1)`,

```text
OPT(B) ≤ Manhattan(B) + 102·(h+3)·√(8h)·n^(5/2 + 1/(4h+2)).
```

| depth `h` | exponent | coefficient | from `n ≥` |
| --- | --- | --- | --- |
| 1 | `8/3` | 1154 | `1.3·10⁸` |
| 2 | `13/5` | 2040 | `1.8·10¹³` |
| 3 | `18/7` | 2998 | `1.7·10¹⁸` |
| 4 | `23/9` | 4039 | `1.5·10²³` |

The main theorem uses the largest depth whose threshold is at most `n`, so
`h ≈ ln n / 11`. `Tree.tree_exponent` states `OPT(B) ≤ Manhattan(B) + C·n^(5/2+ε)`
for every `ε > 0`, with the statistics `Tree.tree_average_optimal_length` and
`Tree.tree_gods_number`. The constants are certified upper bounds, not claims of
optimality.

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
| `SlidingPuzzle/Algorithm/` | Squares of a board of side `k*s`, region counts, local Finish, the residual board after a prefix |
| `SlidingPuzzle/Hub/` | Shared machinery: squares with reservoirs, the abstract state and its relation to boards, the König plan and round walks, the Chernoff order and residence bounds, cleanup, Finish, the statistical reduction (`AsympStats`) |
| `SlidingPuzzle/Tree/LaneSys`, `Hier`, `HierMix`, `Route*` | Lane systems; hierarchies with uniform or per-level branching; routes of tiles |
| `SlidingPuzzle/Tree/Layout*`, `Geom*`, `Op*`, `Simulate` | Lanes on the board; the operations hopR, hopC, jump and insertions |
| `SlidingPuzzle/Tree/Run*`, `Residence` | The abstract run: plan, serves along routes, placeholders, relocations, invariants, residence |
| `SlidingPuzzle/Tree/Preload`, `Transport`, `AsympBound` | Preloading home tiles, the algorithm on side `k*s`, arbitrary sides |
| `SlidingPuzzle/Tree/*Accounting`, `Feasibility`, `Final` | The cost bound `50(h+3)k²s³` and the conditions on `k`, `q`, `s` |
| `SlidingPuzzle/Tree/MixGrid`, `MixLog`, `GridChoice`, `Stats` | Grid choice, the final theorems, statistics |
| `Zhong/` | Word-level puzzle library in the paper's conventions: reachability criterion, orbit statistics, move words |
| `research/exponent/TREE_PLAN.md` | Design of the tree algorithm and map of its proof |

## Proof outline

*Statistics* (`Hub/AsympStats`, `Bridge/Statistics`). As in the paper,
Manhattan distance `M` is a lower bound for `OPT`, its orbit mean is
`(2/3)*n³ + O(n²)`, and its maximum over reachable boards is `n³ + O(n²)`. So
it suffices to show `OPT(B) ≤ M(B) + C·f(n)` for every reachable board, where
`f ≥ n²`: a solution with that many inefficient moves.

*Squares and lanes* (`Tree/Layout`). A board of side `n = k*s` is cut into
`k × k` squares of side `s`, one per target class; tiles of class `x = (a, c)`
belong in square `x`. Zhong's scheme carries tiles in corridors pure in the full
class, `k³n` cells, each tile placed at cost `O(n)`; balancing `n³/k` against
`k³n²` gives `n^(11/4)`. Here the first `q` rows and columns of every square
hold *lane* cells. A tile in band `b` travels along row lanes of its band until
it is in block column `c`, then along column lanes of block column `c` until it
is in band `a`, and drops into the region of the square it lands in.

*The hierarchy* (`HierMix`, `Route`). The `k` blocks of an axis form a tree of
depth `h` with branching `B ℓ` at level `ℓ`, so `k = ∏ B ℓ`. Offset `(ℓ, i)`
carries, inside every level-`ℓ` node, the blocks left of child `i` to its first
block and the blocks right of it to its last block. A hop goes to the near end
of the child containing the target, at the first level where the two blocks
differ, so a tile reaches its class in at most `h` hops per axis. There are
`q = Σ B ℓ` offsets, about `h·b` for branching `b`, and each lane serves a known
set of target classes.

*Plan and serves* (`Tree/RunPlan`, `RunServe`, `Hub/Plan`, `RoundWalk`). The
demand multigraph of the squares, padded with dummy edges, splits into perfect
matchings (Hall/König). In each round every square sends one tile. The edge
`S → D` is served along its route backwards: the last gateway first, the source
last. A gateway inserts a clean stock tile of class `D` if it has one, and
otherwise a free tile as a *placeholder* tagged `D`. So every planned insertion
happens, and the traffic of a round is a fixed function of the round.
Relocations of the blank between cycles are jumps in snake order (`RunReloc`).

*Stock and placeholders* (`RunInv`, `RunRank`). At a gateway, the stock of
`D`-tiles plus those in flight plus the dirty arrivals equals the placeholders
emitted, and a placeholder happens only at stock zero. Summing over the number
of hops left, the placeholders are at most `2h + 1` times the in-flight maxima.

*In flight* (`Tree/Residence`, `RunRes`, `Hub/Chernoff*`, `Hub/InFlight*`).
Lanes are delay lines. The rounds are run in a good order, which exists by a
Chernoff bound for sampling without replacement (Maclaurin's inequality), so
the tiles of each tag in a lane stay within the lane's budget. The residence
time of a tile telescopes over the distance bands it crosses.

*Preload* (`Preload`). Before the plan, three-cycles put into every square the
home tiles it needs as reserve for placeholders and dummies, `52n` moves each.
Initial lane contents are junk and cost `O(n)` each until they drop out.

*Cleanup and Finish* (`Hub/Cleanup`, `FinishGen`). The tiles left outside
their squares are fixed at least two at a time by three-cycles and double swaps,
and every square is solved locally, `k²·O(s³) = O(n³/k)`.

*Cost* (`FineAccounting`). Once `8kq ≤ s`, `16kλ ≤ s` and `2048hk ≤ s`, the
algorithm makes at most `50(h+3)k²s³ ≤ 50(h+3)n³/k` inefficient moves; per
`k²s³`, hops cost `40h`, relocations `≈ 45`, the preload `≈ 51`, cleanup `≈ 29`
and Finish `2.5`. Arbitrary sides are reduced to `k*⌊n/k⌋` by a Parberry prefix
(`O(n²k)`).

*Grid* (`MixGrid`). The conditions ask for `s ≈ 8h·b·k`, i.e. `8h·b·k² ≈ n`.
The first `j` levels branch `b + 2` and the rest `b`, with `b` the largest even
number such that `8h·b^(2h+1) ≤ n` and `j` the largest such that `8qk² ≤ n`.
Then `k` is within a factor `(b+2)/b` of the ideal, and
`n³/k ≤ 1.012·√(8h)·n^(5/2+1/(4h+2))`.

*Depth* (`MixLog`). With the largest `h` such that `8h·256^(2h+1) ≤ n`,
`n^(1/(4h+2)) ≤ 176` and `ln n ≥ 11h + 5.5`, which turns `(h+3)√(8h)` into
`(ln n)^(3/2)`.

[`PROOF_NOTES.md`](PROOF_NOTES.md) relates the construction to the paper and
lists the certified estimates. [`research/exponent/TREE_PLAN.md`](research/exponent/TREE_PLAN.md)
describes the design in more detail and maps it to the Lean files.
[`OPTIMIZATION_IDEAS.md`](OPTIMIZATION_IDEAS.md) lists open improvements.

## Prior work

Zhixian Zhong, *Additive Approximation Algorithms for Sliding Puzzle* (2023),
included as `zhong2023_additive-approximation-sliding-puzzle.pdf`. Its
Proposition 9 gives the same statements with error `O(n^(11/4))`. This project
follows its conventions, its reduction to a boardwise bound, and its division
of the board into squares with reservoirs and a local Finish; the hierarchical
lane transport is new.
