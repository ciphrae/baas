# Further constant reductions

The certified boardwise coefficient is **776** for `n ≥ 4096`
(`Hub.uniform_approximation_explicit`). The large-board proof has the bound

```text
1.144253 · (2 · 1.22660 · 182.186 + 2 · 0.688613 · 167.7 + 2/250)
  ≈ 775.70 < 776,
```

and the cubic solver covers `4096 ≤ n ≤ 2^26 + 2^13` within the same
coefficient (it reaches about `775.03` at the top of that range).
The exponent and the lower threshold `4096` are unchanged.

For more speculative structural changes, see
[BREAKTHROUGH_IDEAS.md](research/exponent/BREAKTHROUGH_IDEAS.md). The leading
proposal tracks tiles through successive distance bands; its rate sum
telescopes and may remove the logarithmic factor from the current algorithm.

## Implemented in the latest pass (19,319 → 776)

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

Each step re-tuned the grid factor `hubA`, the hub threshold and the
certificate constants; [PROOF_NOTES.md](PROOF_NOTES.md) lists the final
estimates.

## Where the bound now comes from

With `A = 182.19` (coefficient of `X = n²s`) and `B = 167.7` (of `Y = k²n²L`),
the constant is `2r(1.22660A + 0.688613B)` with `r ≈ 1.1443`:

- `A`: hops `2·55 = 110`, relocations `66` (a round weighs at most `66k²`
  jump units of `s`), local Finish `5`, remainders `1.2` (mostly `132/k`).
- `B`: bypass jumps `39·1.5467 = 60.3`, cleanup `52·1.5467 = 80.4`,
  terms without the logarithm `≈ 26.6` (at `L = 27`), remainders `≈ 0.4`.

The weighted parts are now `1.2266A ≈ 223.5` and `0.6886B ≈ 115.5`: the local
side dominates, which is why the grid factor dropped to `14`. The three-cycle
constant `52` enters hops (`52s` of `55s`), jumps (`52s` of
`(54 + 39d)s`) and cleanup (`26n` per tile). The threshold `2^26 + 2^13` balances the
two regimes: the hub coefficient falls only slowly above it (about `773` at
`2^27`), while the cubic solver's coefficient grows as `(n/ln n)^(1/3)` and
equals the hub's near `2^26`. Lowering the hub coefficient therefore also
needs a better solver on the initial range (§5).

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

## 3. Upper-tail base

Base `17/16` instead of `9/8` in the upper Chernoff tail (threshold
`(33/32)μ + 12λ`, from `(17/16)^33 ≥ e²`) lowers the logarithmic part of `Rhub`
by about 3% but doubles the `k²λ` remainder; the net gain is under 1%.

## 4. Reserve padding

`Q' = Rhub + 8n + 10` could be about `Rhub + 7n + 6`, since the corridor bound
is used twice in the padding argument. This saves about 2 in `B`.

## 5. Threshold and initial range

The hub coefficient decreases slowly above the threshold, while the cubic
solver's coefficient grows as `(n/ln n)^(1/3)`. A better solver for boards of
side `10^7` to `10^8`, or a hub variant with smaller capacity requirements,
would let the hub regime start lower.
