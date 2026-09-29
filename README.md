# BAAS: Better Approximation Algorithms for Sliding puzzles

A Lean 4 / mathlib proof that Manhattan distance approximates the optimal
solution length of the `n × n` sliding puzzle within `O(n^(5/2) (ln n)^(3/2))`.
This improves the error `O(n^(11/4))` of Proposition 9 in Zhixian Zhong,
*Additive Approximation Algorithms for Sliding Puzzle* (2023), §5.2
(`zhong2023_additive-approximation-sliding-puzzle.pdf`, printed p. 145).

For every reachable board `B` of side `n ≥ 2²³ ≈ 8.4·10⁶`
(`SlidingPuzzle.Tree.tree_lam_approximation`,
[`Tree/LamLog.lean`](SlidingPuzzle/Tree/LamLog.lean)),

```text
OPT(B) ≤ Manhattan(B) + (97·ln n + 2670)·√(ln n)·n^(5/2)
       ≤ Manhattan(B) + 245·n^(5/2)·(ln n)^(3/2)
```

(the second line is `Tree.tree_lam_approximation_uniform`).

Hence, over the reachable orbit of the standard `n × n` target,

```text
average optimal solution length = (2/3)*n³ + O(n^(5/2) (ln n)^(3/2))
God's number                    =       n³ + O(n^(5/2) (ln n)^(3/2))
```

(`Tree.tree_log_average_optimal_length`, `Tree.tree_log_gods_number` in
[`Tree/Stats.lean`](SlidingPuzzle/Tree/Stats.lean)). The leading constant is
`97`; the constant `245` holds uniformly from `2²³` on.

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

The main theorem does not fix the depth in advance: it takes `k ≈ √(n/16λ)`
squares per side, as many as the residence windows allow, `λ = 3(⌊log₂ n⌋ + 1)`, and the
smallest depth whose branching fits the lane budget `q ≤ 2λ`, so
`h ≤ 1 + ln n / 8.56`. `Tree.tree_exponent` states `OPT(B) ≤ Manhattan(B) + C·n^(5/2+ε)`
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
| `SlidingPuzzle/Tree/*Accounting`, `Feasibility`, `Final`, `FineLog`, `FinalLog` | The cost bounds `50(h+3)k²s³` and `(48h+142)k²s³` and the conditions on `k`, `q`, `s` |
| `SlidingPuzzle/Tree/LamGrid`, `LamLog`, `MixGrid`, `GridChoice`, `Stats` | Grid choice, the final theorems, statistics |
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

*Cost* (`FineLog`, `FinalLog`). The run needs `8kq ≤ s` (lane width and event
count) and `16kλ ≤ s` (residence windows, `λ = 3(⌊log₂ n⌋ + 1)`). Under these
alone, with `λ, k ≥ 64`, the algorithm makes at most `(48h + 142)·k²s³ ≤
(48h + 142)·n³/k` inefficient moves; per `k²s³`, hops and stock cost `≈ 47.8h`,
the preload `≈ 51`, relocations `≈ 57`, cleanup and Finish `≈ 32`. Arbitrary
sides are reduced to `k*⌊n/k⌋` by a Parberry prefix (`O(n²k)`).

*Grid* (`LamGrid`). The first `j` levels branch `b + 2` and the rest `b`. The
depth `h` is the smallest one such that `h(b_h + 2) ≤ 2λ`, where `b_h` is the
largest even `b` with `16λ·b^(2h) ≤ n`; then `j` is the largest with
`16λk² ≤ n`. So `q ≤ 2λ` and the lane width costs nothing beyond the residence
windows. Minimality of `h` gives, at depth `h - 1`, a branching
`b` with `(h-1)(b+2) > 2λ` and `b^(2(h-1)) ≤ n < 2^(λ/3)`, hence
`b^12 < 2^(b+2)` and `b ≥ 73`. So `16λ·73^(2(h-1)) ≤ n`, `b_h ≥ 8` and
`λ ≥ 33 + 36(h-1)`. If `b_h ≥ 64` the mixed grid rounds `k` by `(b+2)/b ≤ 33/32`.
Otherwise (just after a change of depth) the upper `h - 1` levels are a mixed grid
of branching `c ≤ 62` sized for `k/64`, and the last level branches `d ≥ 64`
(`Bfree`); `d·c < 64(c+2)` keeps `q ≤ 2λ`. Either way `64n < 1089λk²`.

*Constants* (`LamLog`). The cost is at most `(1 + (33/4)(48h+142)√λ)·n^(5/2)`, and
with `48h + 142 ≤ 5.6075·ln n + 150.6`, `λ ≤ 4.3281·ln n + 3` this is at most
`(97 ln n + 2670)·√(ln n)·n^(5/2)` for `ln n ≥ 15.94`. For the uniform constant
`245` the depths `1` and `2` are bounded directly (depth `2` needs
`n ≥ 16λ(2λ-1)² ≥ 26641200`).

*Fixed depth* (`MixGrid`). With `s ≈ 8h·b·k`, `b` the largest even number such
that `8h·b^(2h+1) ≤ n` and `j` the largest such that `8qk² ≤ n`,
`n³/k ≤ 1.012·√(8h)·n^(5/2+1/(4h+2))`.

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
