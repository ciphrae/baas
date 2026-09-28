# Further constant reductions

The certified boardwise bound is **`OPT(B) ≤ M(B) + 268·n^(8/3)`** for
`n ≥ 1.1·10⁹` (`Hub.uniform_approximation_explicit`).

From `1.1·10⁹` on the capacity condition `76kλ_A ≤ 5s` no longer limits `k`, so
the grid sits at the optimal ratio `k ≈ 0.49·n^(1/3)` and the coefficient is
the asymptotic value of the accounting (`≈ 347.6`). Further progress has to
lower `A` or `B` below; the coefficient scales like `A^(2/3)B^(1/3)`, so one
unit of `A` is worth about `4.2` and one unit of `B` about `0.46`.

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
| Reserve `Rhub + 2n + k² + 6` instead of `Rhub + 8n + 10`: dummies and loops of the reserved rounds are bounded together, and the run's dummy budget is the actual planned count | `538·n^(8/3)` |
| Corridor junk counted by half lengths: `2k²n` instead of `4k²n` (also the initial potential) | `520·n^(8/3)` |
| Near-corner three-cycles: placements cost `8` per unit of distance, so a three-cycle with two tiles near a (reflected) box corner costs `16s + O(k)`; insertions `28s → 10s + O(k)`, jump weight `30 → 13`; start `1.1·10⁹` | `363·n^(8/3)` |
| Corner terms charged exactly (`492k`), a served tile charged hop1 plus hop2 instead of twice the larger | `348·n^(8/3)` |
| Designated cells (two per reservoir, classes recorded): a relocation leg is one strip jump onto a designated cell and a restore (`16 + 7d` instead of `13 + 21d`); dummy relocations `42k → 14k` | `268·n^(8/3)` |

Each step re-tuned the grid, the hub threshold and the certificate constants;
[PROOF_NOTES.md](PROOF_NOTES.md) lists the final estimates.

## Where the bound now comes from

The hub algorithm costs at most `2(A·n²s + B·k²n²)` inefficient moves, with
`A = 55.65` and `B = 251.1` (`hubBound_le_lin`, for `k ≥ 500`). With
`t = k/n^(1/3)` this is `2(A/t + Bt²)·n^(8/3)`, minimal at
`t = (A/2B)^(1/3) ≈ 0.48`, which the grid `70m³ ≤ n` attains.

- `A`: hops `25` (hop1 `13s`: reservoir walk `2s`, strip walk `s`, insertion
  `10s`; hop2 `12s`: walk `2s`, insertion `10s`), relocations `28` (a round
  weighs at most `28k²` jump units of `s`: `7` per served square, `21` per unit
  of snake distance, three strip jumps of `7s` per square of distance), local
  Finish `2.5`, remainders `≈ 0.15`.
- `B`: cleanup of the misplaced tiles, `13n` each (half of `26n`), about
  `9.75k²n` tiles (corridors `2`, stock `1`, bypassed `1.376`, reserve
  `3.376`, junk `2`): `≈ 127`; dummy relocations `84`; bypass jumps
  `21·1.376 ≈ 29`; hop2 crossings `7`; corner terms `≈ 2`; potential `2`.

Each unit of `Rhub/n` costs `47` in `B` (bypass `21`, cleanup `2·13`).

## 1. Reservoir walks

Every operation starts with a walk of the blank inside a reservoir, charged at
its full length `2s`: hop1 to the top left corner, hop2 to a left corner, a
jump to the top left corner. The operations end near various corners (hop1 top
left or right, hop2 top or bottom left, a jump top left). Starting hop1's
vertical jump into the landing strip from the blank's own column bounds walk
and strip walk together by `2s` (`A`: `25 → 24`). Bounding every walk by `O(k)`
(`A` about `55.65 → 51`, coefficient about `335`) needs operations that end
where the next one starts.

## 2. Relocations by one jump

A relocation jumps into `Z`, cycles a class-`y` tile next to the landing cell,
jumps back and jumps the tile across: `21` of the `28` in `A` are these three
jumps. The tile has to be of a class fixed in advance because the abstract run
is computed from class counts only. If each square kept a free tile of a
recorded class on a fixed reservoir cell, one jump would do, and the cell
would be refilled by a near-corner three-cycle (`10s`): relocations about
`28 → 12`, coefficient about `280`. This needs the designated tile in the
abstract state.

## 3. Dummy relocations

A path of a round, cut at a dummy edge, is started by a relocation over up to
`2k` squares (`42k + 18`). Relocating along the dummy edges themselves, with
dummy edges paired by a short matching of surplus and deficit squares, would
lower the average relocation; in the worst case it still grows like `k`.

## 4. Lower-tail threshold

With the merged upper tail the budget is essentially `(41/30)n = (41/40)n/θ`
for the lower-tail threshold `θ = 3/4`. From `1.1·10⁹` on capacity has slack
(`76kλ_A` is about `0.1·5s`), so a larger fixed `θ` is affordable: `θ = 0.85`
needs capacity factor about `50` instead of `15.2` and gives `Rhub ≈ 1.21n`
(`B` about `−8`, coefficient about `−3.5`).

## 5. Cleanup

Cleanup fixes every misplaced tile by whole-board three-cycles (`52n` for two
tiles), whatever its distance to its square. The misplaced tiles are those left
in corridors, the reserve, stock and bypassed tiles and corridor junk.

## 6. Local Finish

Finish solves every square by the `5s³` solver, `2.5` in `A`. For boards whose
squares are themselves above `1.1·10⁹` the explicit bound applies to them
recursively, and Finish becomes a lower-order term.

## 7. Below 8/3: grouped corridors and preloaded home reserves

**Status (2026-09-29): proved.** The many-level version is formalized in
`SlidingPuzzle/Tree/` and `Tree.tree_exponent` gives `OPT <= M + C n^(5/2+eps)`
(see `research/exponent/TREE_PLAN.md`). The two-level proposal below is the
historical starting point; the proved construction uses `b`-ary lanes of any
fixed depth `h`, with exponent `5/2 + 1/(4h+2)`. Constants are unoptimized.

Original proposal: **two routing levels could give
`OPT <= Manhattan + O(n^(13/5))`**. Split the `k` destination blocks into
`sqrt(k)` groups and route to the near boundary of the target group, then
within it. The proposed lane inventory is `O(k^(3/2)n)`, giving the balance
`n^3/k + k^(3/2)n^2` at `k ~= n^(2/5)`.

Two supporting ideas address the extra stages:

- Tagged free placeholders preserve planned insertions. The stock identity
  `S + F + D = B` bounds missing-stock events additively through the stages.
- Preload correctly destined tiles as uneven local reserves, using the
  existing `52n` three-cycle primitive. Preparation costs `O(n)` per tile;
  the correct-home diagonal cancels from demand imbalance, so these reserves
  do not introduce corresponding dummy deficits. This avoids reserving the
  same number of whole rounds everywhere.

The missing results are a lane-weighted bound on classwise in-flight maxima,
the board layout, and complete local/blank/cleanup accounting. Fixed deeper
hierarchies would target `5/2 + 1/(4h+2)`; two levels are the recommended first
attempt. Finite checks passed for monotone routes, the pipeline identity and
home-reserve preparation; no Lean exponent theorem has changed.

See [the detailed proposal](research/exponent/BELOW_EIGHT_THIRDS.md) and
[the reproducible checks](research/exponent/below_eight_thirds_check.py).

### Conditional many-level result

[The extension contract](research/exponent/HIERARCHY_CONDITIONAL.md) now spells
out sufficient hypotheses for every fixed depth `h`. The companion
[Lean file](research/exponent/HierarchyConditional.lean) verifies the resource
recurrence, integer branching, and the conditional implication to
`O_h(n^(5/2 + 1/(4h+2)))`, hence `O_epsilon(n^(5/2+epsilon))`.
Its algorithmic `HierarchyBudget` hypothesis is now discharged by the `Tree` development (with the same exponent `5/2 + 1/(4h+2)`).

All levels should use one original matching plan and one shuffle. Keeping
the final destination as the tag preserves at most one insertion per class
per lane per round and at most `k` insertions per lane. Recursive route
experiments passed through four levels. An additional `O_h(k^3 b)` rounding
inventory term is needed; its cleanup cost is absorbed when `k^2 <= n`.
The next target is a parametric residence lemma for these lane families.
