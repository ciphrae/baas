# The Lean proof of O(n^(8/3))

**Status: complete.** The final theorems in
[`SlidingPuzzle/Hub/Main.lean`](../../SlidingPuzzle/Hub/Main.lean):

| Theorem | Statement |
| --- | --- |
| `Hub.uniform_approximation_explicit` | `OPT(B) ≤ M(B) + 1084·n^(8/3)` for every reachable board, `n ≥ 4096` |
| `Hub.uniform_approximation` | `OPT(B) ≤ M(B) + C·n^(8/3)` for every reachable board, `n ≥ 4096` |
| `Hub.average_optimal_length` | mean optimal length `= (2/3)n³ + O(n^(8/3))` |
| `Hub.gods_number` | God's number `= n³ + O(n^(8/3))` |
| `Hub.average_optimal_length_rpow`, `Hub.gods_number_rpow` | the same errors are `O(n^α)` for every `α ≥ 8/3` |

They depend only on `propext`, `Classical.choice` and `Quot.sound`
(`Checks/Axioms.lean`). The mathematics is `PROOF.md`, written for the earlier
error `O(n^(8/3)(log n)^(1/3))`; this file records how the Lean proof is
organized and where it departs from `PROOF.md`, in particular the segmented
in-flight bound that removes the logarithm. The constants are not claimed
optimal. [PROOF_NOTES.md](../../PROOF_NOTES.md) records the accounting
improvements.

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
   here `s ≥ 8k²`. `Algorithm/Finish*` needs only `8 ≤ side n k`
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
| `ChernoffMaclaurin`, `ChernoffPerm`, `ChernoffChain` | Maclaurin's inequality, subset Chernoff for permutations, nested-set upper tail | tail counts |
| `InFlight*` | push lemma, segmented residence, windows, union bound, telescoping sums | `exists_good_order` |
| `Run*` | ghost roles, stock identity, validity, cost | `exists_valid_run` |
| `Cleanup`, `FinishGen`, `Transport` | cleanup, Finish on the hub layout, the whole algorithm on side `k*s` | `exists_hub_solution` |
| `AsympAccounting`, `AsympBound`, `LinBound`, `LinError`, `AsympStats`, `Main` | accounting, choice of `k`, general sides, statistics | the final theorems |

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
single square). With `B_j` the insertions from distance `≥ j` over the plan,
the band window is `w_j = min Δ (⌊4sΔ/(3B_j)⌋ + 1)` and the residence window
of distance `d` is `W_d = w_0 + … + w_d`. A good order has (a) at least `s`
insertions from distance `≥ j` in every `w_j` consecutive rounds and (b) for
every time `τl`, at most `⌊41 M_x/(40Δ)⌋ + 15λ` insertions of class `x`, counted
over all distances `d`, each in its own window `[τl - W_d, τl]`, where
`M_x = Σ_d A_{x,d}(W_d+1)` and `λ = 3(log₂ n + 1)`. A round inserts class `x`
into a half at most once over all distances (`sum_count_roundIns_le_one`).
* Maclaurin's inequality `e_w(y)/C(N,w) ≤ (Σy/N)^w` (not in Mathlib) is proved
  by induction on the number of elements with Bernoulli's inequality.
* Lower tail (`card_lower_tail_log`) with weights `1 - g/(4K) ≥ (3/4)^(g/K)`
  (Bernoulli) and `log(4/3) ≤ 0.28769` (series): at most
  `Δ!·exp(-0.03423μ/K)` orders have a window sum `≤ (3/4)μ`. With
  `λ_A = log₂(k³s²) + 4` and capacity `76kλ_A ≤ 5s` the `2k³Δ` events (a) have
  total weight at most `1/2`.
* Upper tail for nested sets (`ChernoffChain.lean`): positions carry sets
  `A τ` forming a chain. Removing the position with the largest set, the other
  constrained positions already take values inside it, and swapping
  unconstrained positions makes all remaining values equally likely, so
  `#{σ : σ τ ∈ A τ, τ ∈ S}·n^|S| ≤ n!·Π|A τ|` (`card_goodSet_mul_le`) and the
  moment bound of independent indicators holds. With weights `(21/20)^a` and
  `(21/20)^41 ≥ e²`, at most `Δ!/(21/20)^λ'` orders have a count
  `≥ (41/40)μ + λ'`; `λ' = 15λ`. In (b) the windows all end at `τl`, so the
  rounds counted at a position form a chain.
* All fibres of `σ ↦ σ '' T` have the same size, so subset counts are
  permutation counts; a union bound gives the order: the `2k⁴Δ` events (b)
  number below `n³/2 < 2^λ/2` once `8k ≤ s`.
* Segmented residence (`InFlightSegment.lean`): a tile at position `≤ B` moves
  one step toward the head with every later insertion at a position `≥ B`
  (`seg_bound`). Insertion positions of consecutive distances differ by `s`,
  so with (a) a tile inserted from distance `d` has left band `j` within
  `w_j` rounds of reaching it, and the half within `W_d` rounds of its
  insertion (`last_le_of_segments`); with (b) the tiles of class `x`
  present are few (`newCnt_le_of_segments`).
* Summing (`InFlightSum.lean`): `∑_d G_d ∑_{j≤d} 1/B_j` counts the bands with
  `B_j > 0` (`sum_mul_sum_inv_le`), which lie in the half
  (`card_bands_mul_le`). A half therefore holds at most
  `(41/30)(len + k) + (41/40)k(k+1) + 15kλ` tiles in flight: one slack term
  per class, not per class and distance. With capacity and `k ≥ 100` this is
  `Rhub n = ⌊14n/10⌋ + 1` per hub (`Hub.exists_good_order`).
* `capacity_lower_bounds` proves `log₂ n ≥ 22`, `λ_A ≥ 48`, `s ≥ 72960` and
  `n ≥ 100s` for all admissible hub instances.

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
The certified totals are:

- `transportBound` retains the potential, served, bypass, and relocation
  terms with their actual dimensions.
- `misplacedBound = 2k²·Rhub n + 13k²n + k⁴ + 10k²`.
- Cleanup costs at most `26·n·(misplaced + 2n + 2)` inefficient moves: each
  three-cycle fixes two misplaced tiles and each double swap fixes four.

## Asymptotics

On side `n = k*s`, `hubBound_le_lin` in `AsympAccounting.lean` keeps
transport, cleanup and Finish in one polynomial: for `k ≥ 100` and
`729k ≤ s` (implied by capacity), `1000·hubBound ≤ 182350X + 705800W` with
`X = n²s` and `W = k²n²`. The in-flight budget `1.4n` enters `W` with weight
`91` (bypass jumps `39`, cleanup of in-flight and reserve tiles `2·26`).

For `n ≥ linN = 10⁷`, take `k = 2m` with `m` the largest integer such that
`304m²(log₂(2mn²) + 4) + 10m ≤ 5n` (capacity, since `λ_A ≤ log₂(kn²) + 4`) and
`64m³ ≤ n` (`exists_lin_width`), and `s = ⌊n/k⌋`; then `m ≥ 50`, capacity and
the room condition hold. Solve the outer `n - k*s < k` layers by the Parberry
prefix (`Parberry/Prefix.lean`, `optimalLength_le_hub_residual`).
`optimalLength_le_lin_nat` gives

```text
1000·OPT ≤ 1000·M + 2·182350·n²s + 2·705800·k²n² + 2000·Z,
```

with `Z = (15n² + 3002n + 1)(n - k*s)` the prefix cost.

For the real bound put `x = n^(1/3)` (`cbrtN`). Maximality of `m` gives
`n < 64(m+1)³`, so `x < 4(m+1)`, or capacity fails at `m + 1`. In the second
case `64(m+1)³ ≤ n` gives `2^(Λ-3) ≤ x⁷` for `Λ = log₂(2(m+1)n²) + 4`, hence
`Λ ≤ 0.266x` (`lin_log_le`), and `5x² < 80.864(m+1)² + 2.5`. With `4m ≤ x` and
`x ≥ 215.44` this is `0.244x ≤ m ≤ x/4` (`lin_range`). Multiplied by `m`, the
cost `KX x³/m + 8KW m²` is concave in `m`, so its endpoint values bound it:
`KX x³ + 8KW m³ ≤ 1083.6·1000·m x²` (`lin_core`, an explicit polynomial
certificate). The prefix adds at most `0.1x⁸`, giving
`OPT ≤ M + 1084 n^(8/3)` (`optimalLength_le_linError`).

For `4096 ≤ n ≤ linN` the cubic solver's exact bound
`5n³ + 1509n² + 1505n + 4796` is at most `1084·n^(8/3)` (`cubic_le_linError`;
about `1077` at the top of the range), so `linConstant = 1084` covers every
`n ≥ 4096` (`uniform_approximation_explicit`). Just above `linN` capacity
limits `k`; asymptotically the grid ratio `k/n^(1/3) = 1/2` gives
`2(2·182.35 + 705.8/4) ≈ 1082`.

The statistical reduction of the paper (Section 5) is proved for any error
scale `f ≥ n²` (`AsympStats.lean`). It yields the average and maximum
asymptotics from the boardwise bound; **1084 is the boardwise coefficient**,
not an asserted exact coefficient for the two-sided statistical errors.
