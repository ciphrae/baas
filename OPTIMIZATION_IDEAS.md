# Further constant reductions

The certified boardwise bound is **`OPT(B) ≤ M(B) + 1084·n^(8/3)`** for
`n ≥ 4096` (`Hub.uniform_approximation_explicit`).

The uniform coefficient is set just above `n = 10⁷`, where the hub algorithm
takes over from the cubic solver (about `1077` there). Just above the
threshold the capacity condition `76kλ_A ≤ 5s` limits `k` (certified range
`0.244x ≤ m ≤ x/4`, value `1083.7`); asymptotically the grid gives about `1082`.

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

Each step re-tuned the grid, the hub threshold and the certificate constants;
[PROOF_NOTES.md](PROOF_NOTES.md) lists the final estimates.

## Where the bound now comes from

The hub algorithm costs at most `2(A·n²s + B·k²n²)` inefficient moves, with
`A = 182.35` and `B = 705.8` (`hubBound_le_lin`). With `t = k/n^(1/3)` this is
`2(A/t + Bt²)·n^(8/3)`, minimal near `t = (A/2B)^(1/3) ≈ 0.505`; the grid uses
`t ≤ 1/2`, which costs almost nothing.

- `A`: hops `2·55 = 110`, relocations `66` (a round weighs at most `66k²`
  jump units of `s`), local Finish `5`, remainders `1.35` (mostly `132/k`).
- `B`: cleanup of the misplaced tiles, `26n` each: the reserve and home padding
  (`8k²n`), stock and bookkeeping terms (`5k²n`), in flight and bypassed
  (`2k²·Rhub = 2.8k²n`) and corridors (`2k²n`), together `≈ 463`;
  dummy relocations `156`; bypass jumps `39·1.4 ≈ 54.6`; the potential of
  the initial corridor tiles `30`; remainders `≈ 2.5`.

Each unit of `Rhub/n` costs `91` in `B`. The budget `1.4n` is
`(4/3)·(41/40)·n` plus about `0.03n` of Chernoff slack: the factor `4/3` is the
lower-tail window (`θ = 3/4`), `41/40` the upper-tail factor. The coefficient
scales like `A^(2/3)B^(1/3)`. The reserve padding `8n` per square is the largest
single term of `B`: every free tile set aside and not used is cleaned up at
`26n`. The three-cycle constant `52` still enters hops (`52s` of `55s`), jumps
(`52s` of `(54 + 39d)s`) and cleanup (`26n` per tile).

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
for the lower-tail threshold `θ = 3/4`. A larger `θ` shortens the windows but
needs capacity `θ log 2/e(θ)·kλ_A ≤ s`, `e(θ) = 1 - θ + θ log θ`, which binds
near the threshold. A `θ` depending on `n` (for example `θ → 1` as `n` grows)
would bring the budget toward `n` for large boards (about `1064` asymptotically),
but the uniform coefficient is set near `10⁷`, where a numerical model puts
the best fixed `θ` at about `0.75`.

## 4. Reserve padding

`Q' = Rhub + 8n + 10` could be about `Rhub + 7n + 6`, since the corridor bound
is used twice in the padding argument. Each unit of `n` in the padding costs
`26` in `B` (about `3.7%` of `B`), so this is worth about `1.2%` of the
constant; a reserve sized by the actual corridor contents rather than by
`sqCorridor` could save more.

## 5. Threshold and initial range

The uniform coefficient is set where the cubic solver (`5n^(1/3)`) meets the
capacity-limited hub algorithm, near `n = 10⁷`. The hub algorithm is now
almost flat there (`≈ 1082` to `1084` for `n^(1/3)` between `215` and `300`),
so moving the switch buys little; the asymptotic coefficient (`≈ 1082`) is
only slightly below the uniform one.
