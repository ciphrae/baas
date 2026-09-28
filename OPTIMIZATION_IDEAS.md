# Further constant reductions

The certified boardwise bound is **`OPT(B) ≤ M(B) + 583·n^(8/3)`** for
`n ≥ 10⁹` (`Hub.uniform_approximation_explicit`).

From `10⁹` on the capacity condition `76kλ_A ≤ 5s` no longer limits `k`, so
the grid sits at the optimal ratio `k ≈ 0.52·n^(1/3)` and the coefficient is
the asymptotic value of the accounting (`≈ 582.85`). Further progress has to
lower `A` or `B` below; the coefficient scales like `A^(2/3)B^(1/3)`, so one
unit of `A` is worth about `3.9` and one unit of `B` about `0.54`.

## Implemented so far

The table records the coefficient of `n^(8/3)(ln n)^(1/3)` through the
optimization passes, then the coefficient of `n^(8/3)`.

| Step | Constant |
| --- | --- |
| Upper Chernoff tail needs only `c ln 2 ≥ 1`: threshold `(13/9)μ + λ` | 17,682 |
| `s ≤ k³` gives `ln(kΔ) ≤ (7/4)ln n`; grid factor `64 → 38` | 16,656 |
| Relocations charged `288s(2+d)` instead of `576s(1+d)`; each cycle relocation serves two squares | 9,046 |
| Home tiles pad the free budget only up to `Q'` | 8,109 |
| Both Chernoff tails sharpened (`θ = 15/16`, base `9/8`) | 6,091 |
| Three-cycles staged by Parberry placements: `254n → 52n` | 1,440 |
| Cleanup fixes two misplaced tiles per three-cycle or double swap | 1,272 |
| Strip jumps charged `13(d+1)` instead of `25(d+1)`; aligned relocations are one jump | 1,215 |
| Lower tail `θ = 7/8` (capacity `317kL`), hub regime from `9·2^24` | 1,044 |
| Jumps via a three-cycle in the target square's own box and three strip jumps; hub regime from `3·2^25` | 894 |
| Cleanup: a three-cycle fixes two misplaced tiles, a double swap four (`26n` per tile); lower tail `θ = 5/6` (capacity `169kL`); grid factor `24 → 14`, hub regime from `2^26 + 2^13` | 776 |
| Segmented residence: the in-flight budget is `O(n)`, and the bound becomes `O(n^(8/3))`; lower tail `θ = 3/4` (capacity `48kL`), slack `λ = 3L`; hub regime from `11·2^20` | `1133·n^(8/3)` |
| Upper tail per class over all distances (nested sets), base `21/20`: in-flight budget `2.1756n → 1.4n`; lower tail with exponent `1/4 - (3/4)log(4/3)` and its own `λ_A = log₂(k³s²) + 4`; hub regime from `10⁷` | `1084·n^(8/3)` |
| Local operations charged by displacement (`2·inefficient ≤ length + ΔM`): strip jumps `13(d+1) → 7(d+1)`, box three-cycles `52s → 28s`; cleanup and Finish end at the target, so half their length; `k ≥ 50`, `Rhub = 1.43n`, hub regime from `2·10⁶` | `635·n^(8/3)` |
| Explicit bound from `10⁹`: no cubic fallback, `k ≥ 500`, `Rhub = 1.376n`, grid `57m³ ≤ n` at the optimal ratio | `583·n^(8/3)` |

Each step re-tuned the grid, the hub threshold and the certificate constants;
[PROOF_NOTES.md](PROOF_NOTES.md) lists the final estimates.

## Where the bound now comes from

The hub algorithm costs at most `2(A·n²s + B·k²n²)` inefficient moves, with
`A = 100.65` and `B = 361.96` (`hubBound_le_lin`, for `k ≥ 500`). With
`t = k/n^(1/3)` this is `2(A/t + Bt²)·n^(8/3)`, minimal at
`t = (A/2B)^(1/3) ≈ 0.518`, which the grid `57m³ ≤ n` attains.

- `A`: hops `2·31 = 62` (a three-cycle `28s` plus `3s`), relocations `36` (a
  round weighs at most `36k²` jump units of `s`: `15` per served square, `21`
  per unit of snake distance), local Finish `2.5`, remainders `≈ 0.15`.
- `B`: cleanup of the misplaced tiles, `13n` each (half of `26n`), about
  `17.75k²n` tiles: `≈ 231`; dummy relocations `84`; bypass jumps
  `21·1.376 ≈ 29`; hop2 quadratic terms `14`; transport potential `4`.

Each unit of `Rhub/n` costs `47` in `B` (bypass `21`, cleanup `2·13`). The
jump and three-cycle bounds come from `Path.two_inefficientMoves_le_of_displacement`
and `two_inefficientMoves_le_of_blank_swap`: a path that moves few tiles a short
way is at most about half inefficient. The walk inside a reservoir before a
jump (`2s`) is still charged its full length.

## 1. Cheaper insertions and jumps

Insertions (`insert_by_cycle`) and jumps cycle three cells of one square's box,
one of which is a free choice of reservoir cell. Staging from the box's
reservoir corner, with that tile already at its staging position, would save
one of the three Parberry placements: roughly `52s → 36s`, and about 10% of the
constant. This needs a reflected box embedding and a staging variant with a
pre-positioned tile. A jump or insertion could avoid the three-cycle
altogether if the wanted tile lay in the reservoir, but region tiles may also
sit in the landing strip and the own column piece, where corridor heads drop
in, and the abstract run fixes the moved tile's class before the board is known.

## 2. Distance-aware staging

The three-cycle charges every Parberry placement its worst case `8n`. A
placement bound proportional to the tile's distance, together with a choice of
the staging corner nearest to the tiles and the blank, would lower the
three-cycle constant wherever the three tiles are close, as in insertions.

## 3. Lower-tail threshold

With the merged upper tail the budget is essentially `(41/30)n = (41/40)n/θ`
for the lower-tail threshold `θ = 3/4` (`1.43n` with slack at `k = 50`). A larger `θ` shortens the windows but
needs capacity `θ log 2/e(θ)·kλ_A ≤ s`, `e(θ) = 1 - θ + θ log θ`, which binds
near the threshold. A `θ` depending on `n` (for example `θ → 1` as `n` grows)
would bring the budget toward `n` for large boards. From `10⁹` on capacity
has slack (at `n = 10⁹`, `76kλ_A ≈ 0.3·5s`), so a larger fixed `θ` is
affordable there, or from a higher start.

## 4. Reserve padding

`Q' = Rhub + 8n + 10` could be about `Rhub + 7n + 6`, since the corridor bound
is used twice in the padding argument. Each unit of `n` in the padding costs
`26` in `B` (about `3.7%` of `B`), so this is worth about `1.2%` of the
constant; a reserve sized by the actual corridor contents rather than by
`sqCorridor` could save more.

## 5. Start of the explicit bound

The explicit bound starts at `10⁹` (`hubN = linN`); the cubic fallback and the
capacity-limited grid are gone. From `4096` the same accounting gave `635`
(set near `2·10⁶`, where capacity held `k` at `50`). Starting higher still only
helps through the lower-order terms (already below `0.1`) or through a larger
lower-tail threshold `θ` (§3).
