# Open improvements

The certified bound is **`OPT(B) ≤ M(B) + 3200·n^(5/2)·(ln n)^(3/2)`** for
`n ≥ 8·256³` (`Tree.tree_log_approximation_explicit`), from the per-depth bound
`102(h+3)√(8h)·n^(5/2+1/(4h+2))` for `n ≥ 8h·256^(2h+1)`
(`Tree.tree_uniform_approximation_explicit`). The history of the constants and of
the earlier `O(n^(8/3))` hub bound is in git.

## Where the bound comes from

`treeBound ≤ 50(h+3)·k²s³` (`Tree/FineAccounting.lean`). Per `k²s³`, with the lane
width at its limit `8kq = s`:

| Term | Cost | Source |
| --- | --- | --- |
| Hops | `40h + 5h` | `hopK = 20s + …` per hop, `2h` hops per tile |
| Preload | `≈ 51` | `52n` per reserve tile, reserves `≈ 6k²qs` |
| Relocations | `≈ 45` | `3(s+3)` per unit of weight, `15k²` per round, `s²` rounds |
| Cleanup | `≈ 29` | `26n` per misplaced tile, halved |
| Stock | `≈ 1.5h` | placeholders and dirty arrivals |
| Finish | `2.5` | `5s³` per square, halved |

The coefficient of the final bound is about `2 × 1.012 × (that sum) × √(8h)`,
times `n^(1/(4h+2)) ≤ 176` in the depth choice.

## 1. An explicit decay of the coefficient

`3200` is a uniform constant from `1.3·10⁸` on. Asymptotically the depth choice
gives `n^(1/(4h+2)) → 16` (from `256^((2h+3)/(4h+2))`) and `(h+3)√h → h^(3/2)` with
`h ≈ ln n / 11.09`, so the coefficient tends to about `125`. An explicit version
could state `OPT ≤ M + c(n)·n^(5/2)(ln n)^(3/2)` with `c(n) → 125` given in closed
form, or a short table of constants for ranges of `n`.

## 2. Hops

The leading term `40h` is `hopK ≈ 20s` per hop and `2h` hops per tile. It alone
is the `h` in `(ln n)^(3/2)`, so its constant matters most for large `n`.
Starting each hop where the previous one ended, and inserting by near-corner
three-cycles (`Moves/ThreeCycleNear.lean`), would lower it.

## 3. Preload, relocations, cleanup

These are the `≈ 125` that do not grow with `h`.

- *Relocations* (`≈ 45`): a leg is a jump followed, unless the right tile is
  already on the landing cell, by a three-cycle in a box covering both squares
  (`Tree/OpJump.lean`), charged `3(s+3)` per unit of weight. A designated tile of
  a recorded class on the landing cell of every square would save the
  three-cycle, as designated cells did for the hub algorithm.
- *Preload* (`≈ 51`): the sharp `52n` three-cycle per reserve tile, and reserves
  sized by the full lane budgets.
- *Cleanup* (`≈ 29`): `26n` per misplaced tile, whatever its distance to its square.

## 4. The logarithm

`(ln n)^(3/2)` is `h` from the hops times `√h` from the lane gap `s ≥ 8h·b·k`
(`q ≈ h·b` lane offsets per square). Removing a factor needs either hops whose
total cost does not grow with the depth, or lane offsets shared between levels
so that `q` stays `O(b)`.

## 5. The threshold

`b ≥ 256` comes from the logarithmic slack `2λ ≤ q` (`log_slack_mix`) and
`256h ≤ q`. A finer bound on `λ = 3(log₂ n + 1)` would allow smaller `b`, and
with it a threshold below `1.3·10⁸` and smaller thresholds for every depth.
