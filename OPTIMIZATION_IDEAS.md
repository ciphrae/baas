# Further constant reductions

The certified boardwise coefficient is **19,319** for `n ≥ 4096`. The large-board proof has the bound

```text
2 · 1.139524 · ((599/299) · 2886.937 + 10772.414/4 + 1/1000)
  ≈ 19318.655326 < 19319.
```

The finite initial range has coefficient `18000`, so it does not limit this bound.
The exponent and the thresholds `4096` and `2^39` are unchanged.

## Implemented: relocation remainder and combined rounding

In `RunBounds.lean`, `k ≥ 2` and `s ≥ k` imply `ks ≥ 4`, so
`4(2ks + 1) ≤ 9ks`. Previously `cost_T4` used `2ks + 1 ≤ 3ks`.
Both `cost_T3` and `cost_T4` retain exact tenths by multiplying their
conclusions by ten. Thus `cost_arith` adds
`0.4 + 6 + 3067.2 + 518.4 = 3592` before rounding.
This lowered the generic transport corridor coefficient from `3767` to
`3592`, and the then-certified constant from **27,607 to 27,508**.

## Implemented: retain size-dependent cleanup and transport budgets

`transportBound` and `misplacedBound` in `Run.lean` now retain the original
counting expressions instead of absorbing all dimensions into generic
coefficients. The existing run and board simulation certify these stronger
budgets. `transportBound_le` and `misplacedBound_le` recover the old generic
estimates for callers that only know `k ≥ 2` and `L ≥ 10`.

The final grid has `k ≥ 1196`. A division-remainder argument proves that
the residual side `ks ≥ 2^38`, so its own `L = log₂(ks) + 1 ≥ 39`.
The earlier `cost_arith_large` and `mis_arith_large` give the following
compatibility estimates; the combined bound below is now stronger:

| Estimate | Generic | Large grid |
| --- | --- | --- |
| Transport | `4032X + 3592Y` | `2883X + 2148Y` |
| Misplaced region tiles | `24k²nL` | `22k²nL` |
| Whole hub algorithm | `4042X + 15888Y` | `2893X + 13351Y` |

Here `n = ks`, `X = n²s`, and `Y = k²n²L`. The large transport estimate
uses local coefficient `576 + 2307` and corridor coefficient
`1 + 2 + 2026 + 119`. With the former `7nL` in-flight budget, the misplaced-tile expression was
`21k²nL + 21k²n + k⁴ + 20k²`; its last three terms fit into `k²nL`
on the large grid.

`hubBound_le_large` carries these improvements through cleanup and Finish.
To keep the initial range from limiting the result, `six_cube_le_hubError`
splits at `2^36`, using `ln n ≥ 8` below it and `ln n ≥ 24` above it.
This reduces that branch's coefficient from `24576` to `18000`.
Together these changes lower the final constant from **27,508 to 20,816**,
without changing puzzle paths or adding assumptions to the final theorem.

## Implemented: combined fractional accounting and in-flight budget

`AsympAccounting.lean` combines transport, cleanup, and Finish before final
rounding. Capacity controls the `k⁴` terms jointly, and `k ≥ 1196`, `L ≥ 39`
force `s ≥ 1000000`. The proof keeps thousandths as integer numerators.
This first lowered the constant from **20,816 to 20,648**.

The in-flight proof already bounded the sum by
`4n(1 + (7/5)L) + 8k + 8k²L`. Capacity gives `8k²L ≤ 8n/25`, and
`s ≥ 500` gives `8k ≤ 8n/500`. Consequently its integer budget is now

```text
Rhub n = floor((28nL + 22n)/5) + 1.
```

`Rhub_lower` and `Rhub_upper` certify the rounding, and `Rhub_le_seven`
retains the previous bound for compatibility. The run uses this budget
directly for reserves and bypasses. The exact misplaced-tile expression is
now `3k²·Rhub n + 21k²n + k⁴ + 20k²`.

The resulting certificate is
`1000·hubBound ≤ 2886937X + 10772414Y`. It passes through
`optimalLength_le_hub_scaled` to the final real ceiling, producing
**19,319**. The Chernoff bound and board-level move primitives are unchanged;
the run can reserve fewer rounds.

## 1. Further reduce cleanup's misplaced-tile count

Cleanup still dominates: the `3k²·Rhub n` contribution alone has leading
coefficient `3·(28/5)·508 = 8534.4` in `Y`, before its nonleading terms.
The factor three consists of one stock/bypass budget and two reserve
budgets. Reducing these counts, or fixing multiple misplaced tiles per
cleanup operation, remains the largest target. Preserve the monotone
decrease of `misplaced` and the last-square blank condition.

## 2. Shorten the double-swap path

`exists_double_swap` costs `508n`, twice the `254n` three-cycle bound.
Cleanup invokes it once per misplaced tile. A specialized route using the
geometry of a tile's home square, or tighter staging in `PrimCycle.lean`,
would reduce this dominant contribution. This needs a board-level path
proof preserving the required regions and blank location.

## 3. Tighten the relocation weight estimate

The combined estimate now charges `2305.927X` for local relocation and
`576X` for served operations. Its local relocation coefficient approaches
`2304` as `k` grows; most of the old rounding loss is already removed.
Further substantial savings need a better bound on `W` or cheaper two-jump
relocations in `RunStep.lean`. The estimate must hold for all valid runs,
including bypasses and dummy rounds. Each unit saved in the final local
coefficient reduces the real boardwise coefficient by about `4.56`.

## 4. Tighten the in-flight union bound

The current order uses `λ = 4L` and `Rhub n = floor((28nL + 22n)/5) + 1`, with a union bound over
at most `n⁴` window events. Fewer relevant events, class-dependent window
counts, or a stronger tail estimate could reduce both the reserve and
bypass contributions. This touches `ChernoffPerm.lean`, `InFlight*`, and
the downstream run budgets. Improving the logarithmic order is a separate
major result.

## 5. Couple grid rounding to cost and retune the grid

`cube_X_le_large` uses `(m+1)/m ≤ 599/598`; the corridor term uses the
opposite side of the same interval. Bounding `2886.937X + 10772.414Y` jointly
could avoid charging incompatible worst cases.

After the fractional in-flight improvement, the continuous grid optimum is
near `hubA = 16·10772.414/2886.937 ≈ 59.70`, versus the current `64`.
Holding the rounding factor fixed suggests only about 11 more units of
improvement. This is an estimate: changing the grid requires recertifying
the half-width lower bound, capacity, cube scales, and prefix estimate.
The earlier suggestion to increase the grid factor to about `74` is now
obsolete because the corridor coefficient has fallen substantially.

## 6. Use a side-dependent large-board threshold

The proof switches to the hub scheme at `2^39`. The initial-range bound is
now `18000`, leaving room to improve the large-grid coefficient further.
Several certified ranges could use different grid rounding, logarithm,
and cost bounds. Benchmark the numerical envelope before formalizing it;
the worst case may move between ranges.

## 7. Couple the residual logarithm to the original side

The actual run uses `Lres = log₂(ks) + 1`, but the final cube conversion
replaces it by `L = log₂ n + 1`. Just above a power of two these may differ
by one. The present conversion also uses the uniform bound
`L ≤ 1.479688 ln n`. A joint bound on the residual logarithm and grid costs
could recover this loss without changing the algorithm.

Another candidate is to move the hub threshold up to `2^40`, where the
logarithm ratio and grid rounding are smaller. First sharpen the initial
solver estimate: retain `5n³ + 1509n² + 1505n + 4796` instead of `6n³`
on the upper part of the initial range. Verify numerically that it stays
below the desired uniform coefficient through the new threshold, then
recertify residual size, logarithm, grid, and prefix inequalities. This
has not yet been formalized.
