# Sliding puzzle: Proposition 9 in Lean

A Lean 4 / mathlib formalization of Proposition 9 of Zhixian Zhong,
*Additive Approximation Algorithms for Sliding Puzzle* (2023), §5.2
(`zhong2023_additive-approximation-sliding-puzzle.pdf`, printed p. 145).

Over the reachable orbit of the standard `n × n` target,

```text
average optimal solution length = (2/3)*n³ + O(n^(11/4))
God's number                    =       n³ + O(n^(11/4))
```

These are `SlidingPuzzle.average_optimal_length`, `SlidingPuzzle.gods_number`
and their conjunction `SlidingPuzzle.proposition9` in
[`SlidingPuzzle/Main.lean`](SlidingPuzzle/Main.lean). Both are proved outright:
no `sorry`, no custom axioms, and no hypotheses standing in for mathematical
steps.

The algorithmic heart is an explicit boardwise bound
(`Algorithm.exists_solution_explicit`): for every `n ≥ 10000`, every reachable
board has a legal solution with at most

```text
19.25*n^(11/4) + 62665*n^(5/2)
```

inefficient moves, i.e. of length at most `Manhattan + 38.49*n^(11/4) + 125330*n^(5/2)`.

## Building

Lean `v4.33.1` with mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```sh
lake exe cache get
lake build
lake env lean Checks/Axioms.lean   # prints the axioms of the main results
```

The main results depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

| Path | Contents |
| --- | --- |
| `SlidingPuzzle/Basic`, `Target`, `Paths` | Boards as `Cell n ≃ Tile n`, legal moves, paths, reachability, `optimalLength` |
| `SlidingPuzzle/Manhattan`, `Algorithm/Accounting` | Manhattan potential; `length + M(end) = M(start) + 2*inefficientMoves` |
| `SlidingPuzzle/Statistics`, `StatisticalBounds`, `DistanceEstimates`, `OrbitParity` | Orbit mean and maximum, `M ≤ n³`, parity invariant |
| `SlidingPuzzle/Bridge/` | Transfer of reachability and orbit statistics from the `Zhong` library |
| `SlidingPuzzle/Proposition9`, `Main` | Proposition 9 from a boardwise bound; the final theorems |
| `SlidingPuzzle/Moves/` | Generic legal-move constructions: jumps, carries, translations, exchanges, local solving |
| `SlidingPuzzle/Parberry/` | A Parberry-style solver (`5*n³ + O(n²)`), row/column/layer prefixes |
| `SlidingPuzzle/Algorithm/Partition`, … | The partition of Section 4.1 (generalized to squares of side `s ≥ k³`) and its counts |
| `SlidingPuzzle/Algorithm/Preparation/`, `Preparation` | Phase I |
| `SlidingPuzzle/Algorithm/Transport/`, `Transport` | Phase II (Algorithm 4) |
| `SlidingPuzzle/Algorithm/Arrangement/`, `Arrangement` | Phase III |
| `SlidingPuzzle/Algorithm/Finish/`, `Finish` | Phase IV |
| `SlidingPuzzle/Algorithm/Admissible` | The four phases composed on boards of side `k*s`, `s ≥ k³` |
| `SlidingPuzzle/Algorithm/GeneralSize` | Reduction of arbitrary sides to admissible ones |
| `Zhong/` | Word-level puzzle library from an earlier formalization attempt: reachability criterion, orbit statistics, move words |

## Proof outline

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
`k⁵s² = k³n²`, which agree only when `s = k³`. Twice the inefficient moves are
bounded by `17*k²s³ + 47*k⁵s² + 31264*k*s³`:

| Phase | What it does | Leading inefficiency |
| --- | --- | ---: |
| Preparation | Stage corridor tiles with a column prefix, spread them into the corridors | `11.5*k⁵s²` |
| Transport | Algorithm 4: move tiles between reservoirs through the corridors, at most `n²` transfers, each leaving through the nearer side of its reservoir | `6*k²s³` |
| Arrangement | Exchange corridor families so every tile is in its own square (length 24, halved) | `12*k⁵s²` |
| Finish | Solve each square with the Parberry solver (length 5, halved) | `2.5*k²s³` |

*Arbitrary sides* (`Algorithm/GeneralSize`). Take `k = ⌊(3/5)*n^(1/4)⌋` and
`s = ⌊n/k⌋ ≥ k³`. Only the outer `n - k*s < k` layers need the Parberry prefix,
which is lower order. With `k ≈ c*n^(1/4)` the leading inefficiency is
`(8.5/c + 23.5*c³)*n^(11/4)`; `c = 3/5` is close to the minimizer and gives
`19.25` (the paper's `c = 1` gives `32`).

[`PROOF_NOTES.md`](PROOF_NOTES.md) relates each step to the paper, records where
the formalization departs from the printed argument, and lists directions for
lowering the constant.
