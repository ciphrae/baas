# The Lean proof of O(n^(8/3) (log n)^(1/3))

**Status: complete.** The final theorems in
[`SlidingPuzzle/Hub/Main.lean`](../../SlidingPuzzle/Hub/Main.lean):

| Theorem | Statement |
| --- | --- |
| `Hub.uniform_approximation_explicit` | `OPT(B) ≤ M(B) + 894·n^(8/3)(ln n)^(1/3)` for every reachable board, `n ≥ 4096` |
| `Hub.uniform_approximation` | `OPT(B) ≤ M(B) + C·n^(8/3)(log n)^(1/3)` for every reachable board, `n ≥ 4096` |
| `Hub.average_optimal_length` | mean optimal length `= (2/3)n³ + O(n^(8/3)(log n)^(1/3))` |
| `Hub.gods_number` | God's number `= n³ + O(n^(8/3)(log n)^(1/3))` |
| `Hub.average_optimal_length_rpow`, `Hub.gods_number_rpow` | the same errors are `O(n^α)` for every `α > 8/3` |

They depend only on `propext`, `Classical.choice` and `Quot.sound`
(`Checks/Axioms.lean`). The mathematics is `PROOF.md`; this file records how
the Lean proof is organized and where it departs from `PROOF.md`. The current
certified constant is **894**, about 5.4 billion times smaller than the
original `4,828,800,024,144`. It is not claimed optimal.
[PROOF_NOTES.md](../../PROOF_NOTES.md) records the accounting improvements.

## Departures from PROOF.md

1. **Four primitives.** Every operation is built from walks of the blank
   inside a reservoir rectangle, straight blank walks along a line (a walk may
   also cross a row group by a jump), vertical/horizontal jumps (blank/tile
   swaps across a straight segment, `≤ 13*(dist+1)` moves, opposite colours),
   and three-cycles inside an embedded square sub-board (`52*m` moves for an
   `m × m` box with `m ≥ 6`, `Hub/PrimCycle.lean`; the three tiles are staged
   by sharp Parberry placements, `Moves/ThreeCycleSharp.lean`). There are no
   restoring carries: region
   contents are tracked only as counts per class, so shuffling tiles inside one
   region costs only its length.
2. **Insertion by a three-cycle.** After walking the corridor to the insertion
   cell `v`, the blank jumps into the source reservoir (the tile `W` there moves
   up to `v`); a three-cycle in the source square's `s × s` box then sends
   `T → v`, `W → u`, `U → t`. This removes every parity case of the insertion.
3. **Relocations and bypasses are straight jumps** (`REvent.jump`, same band or
   same block column). A general relocation `E → Z` goes through the corner
   square `(Z.1, E.2)`, which gives one free tile and gets one back. A jump
   goes into `Z`, lines up the wanted region tile of `Z` on a second landing
   cell by a three-cycle inside `Z`'s own box, jumps back, and jumps that tile
   across.
4. **Roles** `sched`, `stock`, `free`, `home`, no tokens. Relocations and
   bypasses move free tiles, so the total of free tiles grows only by junk
   heads, and one invariant keeps every square's free count positive.
5. **Cleanup by three-cycles** (`exists_three_cycle_sharp`, `52·n` moves): with
   the blank in the last square, a misplaced tile of class `Q` goes into square
   `Q` in exchange for a wrong tile there, which goes home through a third
   wrong tile; if it belongs where the first tile was, a double swap
   (`104·n` moves) exchanges the two, with an exchange inside one square for
   parity. `misplaced` drops by at least two each time.
6. **No Preparation.** The blank is first walked into a reservoir
   (`exists_normalize`); the run starts from the board's abstraction, junk
   corridors included.
7. **`k` even**, so a column walk crosses a row group of `k` rows by a jump of
   odd length `k + 1`.
8. **Finish with small squares.** Zhong's partition has squares of side `k³`;
   here `s ≈ k² log n`. `Algorithm/Finish*` needs only `8 ≤ side n k`
   (`Partition.FDims`).

## Architecture

The abstract run and the board meet in `Hub/Interface.lean`: an `IState` records
the class at every corridor position, the class counts of every region and
the blank's square; `REvent` has the three operations `hop1`, `hop2`, `jump`
with preconditions `Pre`, effect `step` and inefficiency budget `cost`.
`Hub/Layout.lean` defines `Rel` (a board realizes an `IState`).

| Files | Content | Main result |
| --- | --- | --- |
| `Basic`, `Interface`, `Layout`, `LayoutAux` | layout arithmetic, `IState`, `Rel`, cell partition and counts | `rel_absState`, `absState_classTotal`, `misplaced_le_of_rel` |
| `Prim*`, `Geom*`, `Op*`, `Simulate` | the operations on boards | `simulate_step`, `simulate_run` |
| `PlanAux`, `Plan` | transportation matrix, Hall, König decomposition with padding | `exists_rounds` |
| `WalkSnake`, `RoundWalk` | snake order, the two-phase walk of a round | `exists_round_events` |
| `ChernoffMaclaurin`, `ChernoffPerm` | Maclaurin's inequality, subset Chernoff for permutations | tail counts |
| `InFlight*` | push lemma, windows, union bound, harmonic sums | `exists_good_order` |
| `Run*` | ghost roles, stock identity, validity, cost | `exists_valid_run` |
| `Cleanup`, `FinishGen`, `Transport` | cleanup, Finish on the hub layout, the whole algorithm on side `k*s` | `exists_hub_solution` |
| `AsympError`, `AsympStats`, `AsympBound`, `Main` | choice of `k`, general sides, statistics | the final theorems |

## Layout

Square `Q = (b, c)`: rows `[b*s, (b+1)*s)`, columns `[c*s, (c+1)*s)`; offsets
`i = row % s`, `j = col % s`.
* `i < k`: row corridor `R(b, i)`. In block `c = i` it is the landing strip
  (region of `(b, c)`); elsewhere it is the left half (`c < i`, position `q` ↔
  column `i*s - 1 - q`) or right half (`c > i`, column `(i+1)*s + q`).
* `i ≥ k`, `j < k`: if `j = b` the own column piece (region), else column
  corridor `C(c, j)`: lower half position `q` ↔ band `j + 1 + q/(s-k)`, row
  offset `k + q%(s-k)`; upper half ↔ band `j - 1 - q/(s-k)`, row offset
  `s - 1 - q%(s-k)`.
* `i, j ≥ k`: reservoir (region).
`regionSize = s² - sqCorridor`, `sqCorridor = (k-1)*s + (k-1)*(s-k) ≤ 2ks`.
Insertion positions: hop1 at `(d+1)s - 1` (right) or `(d+1)s - 1 - k` (left),
the source block's column farthest from the hub; hop2 at `(|h.1 - D.1| - 1)(s-k)`,
the first cell of the column half inside the hub's band.

## Board operations (`Simulate`)

* **hop1 S h y**: walk in `h`'s reservoir; jump to the landing strip; walk the
  row through the strip into the half up to position `p` (the head drops into
  the strip); jump down into `S` and place the class-`y` tile by a three-cycle.
  Inefficiency `≤ 55s + 26(k+1) + junkRow`: a clean row tile moves toward
  its target block column, so only strip steps and junk steps can be
  inefficient (`PrimWalk.lean` bounds a walk step by step).
* **hop2 h D y**: walk in `D`'s reservoir; jump to the own column piece and
  across a row group into position `0`; walk the column half, crossing row
  groups by jumps of length `k + 1`; jump into `h`'s reservoir and place the
  tile by a three-cycle. `≤ 54s + 13k² + 65k + 78 + junkCol`.
* **jump E Z y**: align in `E`'s reservoir, jump into `Z`, a three-cycle in
  `Z`'s box putting the class-`y` tile on a second landing cell `z'`, jump back
  to `E`, jump to `z'`. `≤ 2s + 26(d·s + 2) + 52s + 13(d·s + 6) ≤ (s+3)(54 + 39d)`,
  `d = sqDist` (`jump_ends2`).
The budgets exposed by `IState.cost` and verified by `OpHop1`, `OpHop2`,
and `OpJump` are:

| Operation | Inefficiency budget |
| --- | --- |
| `hop1` | `55s + 26(k+1) + junkRow` |
| `hop2` | `54s + 13k² + 65k + 78 + junkCol` |
| `jump E Z` | `(s+3)(54 + 39·sqDist E Z)` |
| General relocation through a corner | `(s+3)(108 + 39·sqDist E Z)` |

Region counts are rewritten as sums over tiles (`PrimCount.lean`), so moves
inside one region leave them unchanged and one- and two-tile moves give exactly
`incCnt`/`decCnt`.

## Plan and round walk

`exists_rounds`: a dummy matrix with row sums `(recv - sends)⁺` and column sums
`(sends - recv)⁺` (transportation, induction on the total) plus loops makes all
row and column sums `Δ0 = max_S max(sends, recv)`; Hall
(`Finset.all_card_le_biUnion_card_iff_exists_injective`) gives a permutation
in the support; subtract and recurse. Edges are labelled real while `T` still
has a positive entry.

`exists_round_events`: phase 1 starts a walk at every square with a dummy edge
and a real in-edge; phase 2 starts, in snake order, at every unserved square
with a real in-edge and walks until the cycle closes. Invariants: after phase 1
no unserved square with a real in-edge lies on a cycle with a dummy edge, so
phase-2 walks end where they start. A relocation weighs `54 + 39·sqDist` when
its squares are aligned (one jump) and `108 + 39·sqDist` otherwise, and costs
`(s+3)` per unit. Relocations weigh `≤ 78k + 30` per dummy edge in phase 1; in
phase 2 they telescope along the snake order
(`sqDist P Q ≤ |snake P - snake Q|`), only row changes need a second jump, and
each serves at least two new squares, so a round weighs at most
`66k² + 132k + 30 + (78k + 30)·#dummy`.

## In-flight bound

Per half and block distance `d` a round inserts at most once (the source is a
single square). With `B_d` the insertions from distance `≥ d` over the plan and
window `w_d = min Δ (⌊8(p_d+1)Δ/(7B_d)⌋ + 1)`, a good order has (a) at least
`p_d + 1` insertions from distance `≥ d` in every `w_d` consecutive rounds and
(b) at most `⌊17A_{x,d}(w_d+1)/(16Δ)⌋ + 6λ` rounds inserting class `x` from
distance `d` in every `w_d + 1` consecutive rounds, `λ = 4(log₂ n + 1)`.
* Maclaurin's inequality `e_w(y)/C(N,w) ≤ (Σy/N)^w` (not in Mathlib) is proved
  by induction on the number of elements with Bernoulli's inequality.
* Lower tail with weights `1 - g/(8K)` and `exp(-(134/125)v) ≤ 1 - v` on
  `[0, 1/8]`: at most `Δ!·exp(-31μ/(4000K))` orders have a window sum
  `≤ (7/8)μ`. Upper tail with weights `1 + a/8 = (9/8)^a`: since
  `(9/8)^17 ≥ e²`, at most `Δ!/(9/8)^λ'` orders have a window sum
  `≥ (17/16)μ + λ'`; `λ' = 6λ` covers the union bound.
* All fibres of `σ ↦ σ '' T` have the same size, so subset counts are
  permutation counts; a union bound gives the order.
* Push lemma: a tile inserted at `p_d` leaves after `p_d + 1` insertions at
  positions `≥ p_d`; with (a) it leaves within `w_d` rounds; with (b) the tiles
  of class `x` from distance `d` present are few.
* The room condition bounds the total event count by `n⁴`, so `λ = 4L`
  suffices for the union bound.
* Harmonic sums give at most `(17/14)n(1 + ln(kΔ)) + (17/4)k + 48k²L` per hub.
  With `s ≤ k³`, `ln(kΔ) ≤ (7/4)ln n + 1/s²` (`log_kΔ_le_sharp`).
  The capacity hypothesis `317kL ≤ s` and the room condition give
  `Rhub n = ⌊(14730nL + 13743n)/10000⌋ + 1` (`Hub.exists_good_order`).
  Capacity bounds `48k²L` by `48n/317`; `s ≥ 500` bounds `(17/4)k`.
  `Rhub_lower` and `Rhub_upper` certify the integer rounding, while
  `Rhub_le_seven` recovers the old `7nL` estimate.
* `capacity_lower_bounds` proves `L ≥ 10`, `s ≥ 500`, and `n ≥ 1000`
  for all admissible hub instances.

## The run

`T S D = cnt S D`; `exists_rounds`; the first
`Q' = min Δ0 (Rhub n + 8ks + 10)` rounds are set aside (their real edges' tiles
start as free, padded with home tiles up to `Q'` in total); the other rounds are ordered by
`exists_good_order` and walked by `exists_round_events`; each high-level event
is resolved into operations:
* `serve S D`, same block column: `hop2 S D D`; same band: `hop1 S D D`;
  otherwise, hub `h = (S.1, D.2)`: `hop2 h D D` if `h` has class-`D` stock, else
  the bypass `jump D h y`, then `hop1 S h D`;
* `reloc E Z`: one jump, or two through the corner `(Z.1, E.2)`.
Facts proved:
* `recv - sends = sqCorridor - corrCount + [blank] - [last]` (from the class and
  region totals), so dummy out-edges are `≤ 2ks + 1` per square,
  `free0 ≥ Q' - 2·sqCorridor - 2` and `Δ0 ≤ s² + 1`;
* stock identity `stock + new = out + byp` between high-level events (for
  `x ≠ h` in `h`'s column), so bypasses happen only at stock `0` and
  `byp ≤ N + 1` with `N` from the in-flight bound (the run's insertion list is
  `Consistent` by construction);
* one invariant `free0 + sent + [blank started here] ≤ Σfree + Σbyp + served + [blank here]`,
  with `served ≤ sent + (#dummy rounds so far) + 1`, keeps free counts positive;
* the cost potential `Σ_{junk positions} (q+1)`: each hop's junk term is
  exactly its drop, and inserted tiles are clean.
With `L = log₂ n + 1`, the certified totals are:

- `transportBound` retains the potential, served, bypass, and relocation
  terms with their actual dimensions; the coarser compatibility bounds
  `transportBound_le` (`4032·n²s + 3592·k²n²L`) and `transportBound_le_large`
  (`2883·n²s + 2148·k²n²L` when `k ≥ 1000` and `L ≥ 39`) still hold.
- `misplacedBound = 2k²·Rhub n + 13k²n + k⁴ + 10k²`; it is bounded by
  `24k²nL` generically and by `22k²nL` when `L ≥ 39`.
- Cleanup costs at most `52·n·(misplaced + 2n + 2)` inefficient moves.

`Hub.cost_arith` separates the local coefficient `576 + 3456`
from the corridor coefficient `0.4 + 6 + 3067.2 + 518.4`, using `L ≥ 10`.
`Hub.mis_arith` bounds the leading `21k²nL` and the remaining terms
by `24k²nL`. The large-grid variants `cost_arith_large` and
`mis_arith_large` retain the stronger dimension and logarithm bounds.
These arithmetic lemmas are in `RunBounds.lean`.

## Asymptotics

On side `n = k*s`, with `s ≥ 500`, `hubBound_le_sharp` gives the coarse
`hubBound n k s ≤ 4042·n²s + 15888·k²n²L`. The certified bound uses the
combined `hubBound_le_scaled` in `AsympAccounting.lean`: for `k ≥ 106`,
`L ≥ 26` and capacity `317kL ≤ s`,
`1000·hubBound ≤ 182251X + 255642Y` with `X = n²s` and `Y = k²n²L`. It keeps
transport, cleanup and Finish in one polynomial and uses capacity for the
`k⁴` remainders; capacity also gives `s ≥ 873652`, making the Finish
remainders small.

For `n ≥ 3·2^25`, take `k = 2m` with `24·m³L ≤ n < 24(m+1)³L` and
`s = ⌊n/k⌋`. Solve the outer `n - k*s < k` layers by the Parberry prefix
(`Parberry/Prefix.lean`). The threshold guarantees `m ≥ 53`
(`half_width_large`, split at `2^27`), so grid rounding loses at most `54/53`;
`8L ≤ 5m` (`log_le_half_width`), hence `s ≤ k³` (`div_le_cube_large`); and
`1268m²L ≤ n`, hence capacity. The residual side satisfies `ks ≥ 2^25`, so
its own logarithm satisfies `log₂(ks) + 1 ≥ 26`. The residual estimates
extend monotonically to the original side `n`.

`optimalLength_le_hub_scaled` keeps three terms separate:

| Term | Definition | Cube bound |
| --- | --- | --- |
| `X` | `n²s` | `(100000X)³ ≤ 146947³n⁸L` |
| `Y` | `k²n²L` | `(10⁶Y)³ ≤ 480750³n⁸L` |
| `Z` | `(15n² + 3002n + 1)(n - k*s)` | `(350Z)³ ≤ n⁸L` |

The solution length is at most `M + 2·182.251X + 2·255.642Y + 2Z`.
The natural-number theorem multiplies this inequality by `1000`, preserving
all coefficients until the final real conversion.
On this range, `L ≤ 1.496129 ln n` (`natLog_succ_le_grid_log`, split at
`2^27`), bounded by the cube of `1.143729`. The coefficient is therefore

```text
1.143729·(2·1.46947·182.251 + 2·0.48075·255.642 + 2/350) ≈ 893.74.
```

`hubLargeConstant` is `894`; `hubLargeConstant_rounding` verifies the exact
ceiling. For `4096 ≤ n ≤ 3·2^25` the cubic solver's exact bound
`5n³ + 1509n² + 1505n + 4796` is at most `894·hubError n`
(`cubic_solver_le_hubError`, split at `2^20`, `2^25` and `2^26`), so
`hubConstant = 894` covers every `n ≥ 4096`; `hubConstant_eq` exposes the
value and `uniform_approximation_explicit` proves the resulting bound.
`hubBound_le`, `hubBound_le_large`, `optimalLength_le_hub_sharp`,
`optimalLength_le_hub`, and `le_hubError_of_cube` retain
coarser forms of the estimates.

The statistical reduction of the paper (Section 5) is proved for any error
scale `f ≥ n²` (`AsympStats.lean`). It yields the average and maximum
asymptotics from the boardwise bound; **894 is the boardwise coefficient**,
not an asserted exact coefficient for the two-sided statistical errors.
