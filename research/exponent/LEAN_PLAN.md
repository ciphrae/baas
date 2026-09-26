# The Lean proof of O(n^(8/3) (log n)^(1/3))

**Status: complete** (branch `exponent-research`). The final theorems in
`SlidingPuzzle/Hub/Main.lean`:

| Theorem | Statement |
| --- | --- |
| `Hub.uniform_approximation` | `OPT(B) ≤ M(B) + C·n^(8/3)(log n)^(1/3)` for every reachable board, `n ≥ 4096` |
| `Hub.average_optimal_length` | mean optimal length `= (2/3)n³ + O(n^(8/3)(log n)^(1/3))` |
| `Hub.gods_number` | God's number `= n³ + O(n^(8/3)(log n)^(1/3))` |
| `Hub.average_optimal_length_rpow`, `Hub.gods_number_rpow` | the same errors are `O(n^α)` for every `α > 8/3` |

They depend only on `propext`, `Classical.choice` and `Quot.sound`
(`Checks/Axioms.lean`). The mathematics is `PROOF.md`; this file records how
the Lean proof is organized and where it departs from `PROOF.md`. Constants
are generous and unoptimized.

## Departures from PROOF.md

1. **Four primitives.** Every operation is built from walks of the blank
   inside a reservoir rectangle, straight blank walks along a line (a walk may
   also cross a row group by a jump), vertical/horizontal jumps (blank/tile
   swaps across a straight segment, `≤ 25*(dist+1)` moves, opposite colours),
   and three-cycles inside an embedded square sub-board (`3022*m` moves for an
   `m × m` box, `Hub/PrimCycle.lean`). There are no restoring carries: region
   contents are tracked only as counts per class, so shuffling tiles inside one
   region costs only its length.
2. **Insertion by a three-cycle.** After walking the corridor to the insertion
   cell `v`, the blank jumps into the source reservoir (the tile `W` there moves
   up to `v`); a three-cycle in the source square's `s × s` box then sends
   `T → v`, `W → u`, `U → t`. This removes every parity case of the insertion.
3. **Relocations and bypasses are straight jumps** (`REvent.jump`, same band or
   same block column). A general relocation `E → Z` goes through the corner
   square `(Z.1, E.2)`, which gives one free tile and gets one back. A jump
   fetches any region cell of `Z` by a three-cycle in a box covering both
   squares.
4. **Roles** `sched`, `stock`, `free`, `home`, no tokens. Relocations and
   bypasses move free tiles, so the total of free tiles grows only by junk
   heads, and one invariant keeps every square's free count positive.
5. **Cleanup by double swaps** (`exists_double_swap`, `6044·n` moves): with the
   blank in the last square, a misplaced tile of class `Q` is exchanged with a
   wrong tile of square `Q`, together with an exchange inside one square for
   parity; `misplaced` drops by at least one each time.
6. **No Preparation.** The blank is first walked into a reservoir
   (`exists_normalize`); the run starts from the board's abstraction, junk
   corridors included.
7. **`k` even**, so a column walk crosses a row group of `k` rows by a jump of
   odd length `k + 1`.
8. **Finish generalized.** `Algorithm/Finish*` needed only `8 ≤ side n k`, not
   `k³ ≤ side n k`; it now takes `Partition.FDims` (`Dims.toFDims` keeps the
   11/4 development unchanged), since here `s ≈ k² log n`.

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
  Inefficiency `≤ 3025 s + 50(k+1) + junkRow`: a clean row tile moves toward
  its target block column, so only strip steps and junk steps can be
  inefficient (`PrimWalk.lean` bounds a walk step by step).
* **hop2 h D y**: walk in `D`'s reservoir; jump to the own column piece and
  across a row group into position `0`; walk the column half, crossing row
  groups by jumps of length `k + 1`; jump into `h`'s reservoir and place the
  tile by a three-cycle. `≤ 3024 s + 25(k+2)(k+4) + junkCol`.
* **jump E Z y**: align in `E`'s reservoir, one jump into `Z`, a three-cycle in
  a box covering both squares. `≤ 2s + 25(d·s + 2) + 3022(d+1)s`, `d = sqDist`.
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
phase-2 walks end where they start; relocations cost `≤ 2k` per dummy edge in
phase 1 and telescope along the snake order in phase 2
(`sqDist P Q ≤ |snake P - snake Q|`): `≤ 4k² + 4k(1 + #dummy)` per round.

## In-flight bound

Per half and block distance `d` a round inserts at most once (the source is a
single square). With `B_d` the insertions from distance `≥ d` over the plan and
window `w_d = min Δ (⌊2(p_d+1)Δ/B_d⌋ + 1)`, a good order has (a) at least
`p_d + 1` insertions from distance `≥ d` in every `w_d` consecutive rounds and
(b) at most `⌊2A_{x,d}(w_d+1)/Δ⌋ + λ` rounds inserting class `x` from distance
`d` in every `w_d + 1` consecutive rounds, `λ = 7(log₂ n + 1)`.
* Maclaurin's inequality `e_w(y)/C(N,w) ≤ (Σy/N)^w` (not in Mathlib) is proved
  by induction on the number of elements with Bernoulli's inequality.
* Lower tail with weights `1 - g/(4K)` (only `exp x ≥ 1 + x` is needed):
  `≤ Δ!·exp(-μ/(12K))`; upper tail with weights `1 + a = 2^a`.
* All fibres of `σ ↦ σ '' T` have the same size, so subset counts are
  permutation counts; a union bound gives the order.
* Push lemma: a tile inserted at `p_d` leaves after `p_d + 1` insertions at
  positions `≥ p_d`; with (a) it leaves within `w_d` rounds; with (b) the tiles
  of class `x` from distance `d` present are few.
* Harmonic sums `Σ_d G_d/B_d ≤ H(B_0)` give about `34·n(log₂ n + 1)` per hub,
  under `Rhub n = 200·n(log₂ n + 1)`.

## The run

`T S D = cnt S D`; `exists_rounds`; the first
`Q' = min Δ0 (Rhub n + 8ks + 10)` rounds are set aside (their real edges' tiles
and `min(home0, Q')` home tiles start as free); the other rounds are ordered by
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
Actual totals: cost `≤ 72000·n²s + 1.8·10⁶·k²n²(log₂ n + 1)` (budget
`transportBound = 10⁷(n²s + k²n²(log₂ n + 1))`); region tiles outside their
squares `≤ 643·k²n(log₂ n + 1)` (budget `misplacedBound`, `1000`).

## Asymptotics

`hubBound n k s ≤ 10⁸(n²s + k²n²(log₂ n + 1))` on side `n = k*s`. For `n ≥ 4096`
take `k = 2m` with `256·m³(log₂ n + 1) ≤ n < 256(m+1)³(log₂ n + 1)` and
`s = ⌊n/k⌋`, solve the outer `n - k*s < k` layers by the Parberry prefix
(`Algorithm/GeneralSize.lean`), and bound each term's cube by
`6036³ n⁸ (log₂ n + 1)`, with `log₂ n + 1 ≤ 3 ln n`. The statistics wrapper
of `Proposition9.lean` is generalized to any error scale `f ≥ n²`
(`AsympStats.lean`).
