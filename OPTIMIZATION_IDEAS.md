# Open improvements

The certified bound is **`OPT(B) ≤ M(B) + (97·ln n + 2670)·√(ln n)·n^(5/2)`**, hence
`245·n^(5/2)·(ln n)^(3/2)`, for `n ≥ 2²³` (`Tree.tree_lam_approximation`,
`Tree.tree_lam_approximation_uniform`). At a fixed depth `h` the bound is
`102(h+3)√(8h)·n^(5/2+1/(4h+2))` for `n ≥ 8h·256^(2h+1)`
(`Tree.tree_uniform_approximation_explicit`). The history of the constants (`117`,
`4100`, `375` with the rounding `5/4`, last in `98d0947`; `3200·n^(5/2)(ln n)^(3/2)`
in `Tree/MixLog.lean`, last in `4d9b041`) and the `O(n^(8/3))` hub bound are in git.

## Where the bound comes from

`treeBound ≤ (48h + 142)·k²s³` (`Tree/FineLog.lean`) once `8kq ≤ s` and `16kλ ≤ s`,
`λ = 3(⌊log₂ n⌋ + 1)`. Per `k²s³`, at `8kq = s` and `16kλ = s`:

| Term | Cost | Source |
| --- | --- | --- |
| Hops | `40h + 5h + 1.3h` | `hopK = 20s + 20k(q+2) + 600k + …` per hop, `2h` hops per tile |
| Stock | `≈ 1.5h` | placeholders and dirty arrivals |
| Preload | `≈ 51.3` | `52n` per reserve tile, reserves `≈ 6k²qs + 30λk³q` |
| Relocations | `≈ 57.2` | `3(s+3)` per unit of weight: `45` for the rounds, `10.7` for lane cells, `1.4` from `k ≥ 64` |
| Cleanup, Finish | `≈ 32` | `26n` per misplaced tile and `5s³` per square, halved |

The grid (`Tree/LamGrid.lean`, `optimalLength_le_fine`) has `64n < 1089λk²`, so
`n³/k ≤ (33/8)√λ·n^(5/2)`, and the error is at most `(1 + (33/4)(48h + 142)√λ)·n^(5/2)`.
With `h ≤ 1 + (ln n - 7.04)/8.56` and `√λ ≈ 2.08√(ln n)` the leading constant is
`8.25 · 48/8.56 · 2.08 ≈ 96.3`, and the constant part `142 + 8.5` gives the
`2670·√(ln n)`, which dominates up to `n ≈ e^27`.

## 1. The rounding factor

`33/32` comes from a last level of branching at least `64`. A model of the best
branching vectors (one free level over a mixed grid) rounds by at most `1.003` in the
bulk; `d ≥ 128` where the budget allows would give `65/64`, about `1.5%`.

## 2. The depth and the uniform constant

`245` is attained just after the change to depth `2` (`n ≈ 2.7·10⁷`, `λ = 75`), and
uses `λ ≤ 4.3281 ln n + 3`; the exact `λ` there gives `241`. A numerical model of the
proved inequality `(1 + (33/4)(48h+142)√λ)/(ln n)^(3/2)` gives `209` at `2²³` (depth
`1`) and about `206` at the change to depth `3`.

The actual cost of the construction is lower: the model gives at most `≈ 228` for
`n ≥ 2²³`, and `≈ 213` if depth `1` is kept past the budget, with `q = k > 2λ` and
`k` limited by `8k³ ≤ n` instead of `16λk² ≤ n` (`optimalLength_le_lanes_log` already
takes the two constraints separately). Such a rule, choosing between depth `h` within
the budget and depth `h - 1` over it, would flatten the peaks at the changes of depth.

## 3. Hops

`46.3h` of the `48h` is `hopK ≈ 20s` per hop and `2h` hops per tile. Starting each
hop where the previous one ended, and inserting by near-corner three-cycles
(`Moves/ThreeCycleNear.lean`), would lower it.

## 4. Preload, relocations, cleanup

These are the `≈ 142` that do not grow with `h`, and through `2670·√(ln n)` they
dominate for all practical `n`.

- *Relocations* (`≈ 57`): a leg is a jump followed, unless the right tile is
  already on the landing cell, by a three-cycle in a box covering both squares
  (`Tree/OpJump.lean`), charged `3(s+3)` per unit of weight. A designated tile of
  a recorded class on the landing cell of every square would save the
  three-cycle, as designated cells did for the hub algorithm (`Hub/OpRJump.lean`
  and `IState.des` in `Hub/Run.lean`, last present in commit `37a39f3`).
- *Preload* (`≈ 51`): the sharp `52n` three-cycle per reserve tile, and reserves
  sized by the full lane budgets.
- *Cleanup* (`≈ 29`): `26n` per misplaced tile, whatever its distance to its square.

## 5. The logarithm

`(ln n)^(3/2)` is now `h·√λ`: `h ≈ ln n / (2 ln b)` hops per axis, and `√λ` from
the residence windows `16kλ ≤ s` (a Chernoff bound over about `n³` events,
`Tree/Residence.lean`). The branching cannot grow with `n` because the lanes must
fit the budget `q = h·b ≤ 2λ`, so `b ≈ 12 log₂ b ≈ 73`. Removing a factor needs
hops whose total cost does not grow with the depth, residence windows of width
`o(k log n)` (fewer events, or batches smaller than `k` per round), or lane
offsets shared between levels.

## 6. The threshold

`2²³` comes from `k ≥ 64` (via `n ≥ 102400λ`) and `λ ≥ 64` in the accounting.
Both only enter lower-order terms, so smaller thresholds cost little in the
constants.
