# Open improvements

The certified bound is **`OPT(B) ≤ M(B) + (117·ln n + 4100)·√(ln n)·n^(5/2)`**, hence
`375·n^(5/2)·(ln n)^(3/2)`, for `n ≥ 2²³` (`Tree.tree_lam_approximation`,
`Tree.tree_lam_approximation_uniform`). At a fixed depth `h` the bound is
`102(h+3)√(8h)·n^(5/2+1/(4h+2))` for `n ≥ 8h·256^(2h+1)`
(`Tree.tree_uniform_approximation_explicit`). The history of the constants, the
earlier `3200·n^(5/2)(ln n)^(3/2)` (`Tree/MixLog.lean`, last present in `4d9b041`) and
the `O(n^(8/3))` hub bound are in git.

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

The grid (`Tree/LamGrid.lean`) has `n < 25λk²`, so `n³/k ≤ 5√λ·n^(5/2)`, and the
error is at most `(1 + 10(48h + 142)√λ)·n^(5/2)`. With `h ≤ 1 + ln n/8.56` and
`√λ ≈ 2.08√(ln n)` the leading constant is `10 · 48/8.56 · 2.08 ≈ 117`, and the
constant part `142 + 48` gives the `4100·√(ln n)`, which dominates up to
`n ≈ e^35`.

## 1. The rounding factor

`n < 25λk²` uses `(b+2)/b ≤ 5/4` for the mixed grid, which holds since `b_h ≥ 8`.
Minimality of the depth gives `(b_h + 2)^h > 73^(h-1)`, so `b_h` tends to about `72` as
`h` grows and the factor to `1.03`. An estimate by ranges of `h` would bring the
leading constant from `117` towards `96`.

## 2. The depth bound

`h - 1 ≤ ln n / (2 ln 73)` uses only `b ≥ 73` at depth `h - 1`. For small `n` the
actual depth is lower (the model gives `h = 2` at `10⁸`, where the bound allows `3`),
and a table of `h` for ranges of `n` would sharpen the uniform constant `375`.
A numerical model of `treeBound` with the best parameters gives a coefficient of
about `145` at `n = 10⁸`, `117` at `10²⁰` and `96` at `10¹⁰⁰`.

## 3. Hops

`46.3h` of the `48h` is `hopK ≈ 20s` per hop and `2h` hops per tile. Starting each
hop where the previous one ended, and inserting by near-corner three-cycles
(`Moves/ThreeCycleNear.lean`), would lower it.

## 4. Preload, relocations, cleanup

These are the `≈ 142` that do not grow with `h`, and through `4100·√(ln n)` they
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
