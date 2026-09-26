# Lean plan: O(n^(8/3) (log n)^(1/3)) via hub transport

This is the blueprint for formalizing `PROOF.md`. The skeleton is in
`SlidingPuzzle/Hub/*.lean`: every definition is final, every interface theorem
is stated and currently `sorry`. Modules only communicate through these
statements. Read `PROOF.md` first for the mathematics; this file records where
the formalization deliberately differs (simplifications) and how each module
should be proved.

## Differences from PROOF.md (simplifications for Lean)

1. **Operations are built from four primitives only**: walks of the blank inside
   a reservoir rectangle (`exists_blank_access_path_preserving`), straight blank
   walks along a line (`exists_line_walk`), vertical/horizontal jumps
   (`exists_vertical_jump`, `exists_horizontal_jump`: blank/tile swap across a
   straight segment, length `≤ 25*(dist+1)`, requires opposite colours) and
   **three-cycles inside an embedded square sub-board** (`exists_three_cycle`
   lifted by `Path.exists_embedded`: cost `3022*m` for an `m × m` box). No
   restoring carries. Reservoir contents are tracked only as counts, so moving
   tiles around inside one region is free (it only costs its length).
2. **The inserted tile is placed by a three-cycle**: after walking the row to the
   insertion cell `v`, the blank jumps down into the source's reservoir (the tile
   `W` there moves up to `v`), then a three-cycle in the source square's `s × s`
   box sends `T → v`, `W → u`, `U → t` for some other region cell `u`. This
   removes every parity case distinction of the insertion.
3. **Relocations and bypasses are straight jumps** (`REvent.jump`): same band or
   same block column. A general relocation `E → Z` is two jumps through the
   corner square `(Z.1, E.2)`; the corner square gives one free tile and gets one
   back. A jump fetches an arbitrary region cell of `Z` with a three-cycle in a
   box covering both squares (side `≤ (1 + sqDist) * s`).
4. **Roles**: `sched`, `stock`, `free`, `home` (no tokens). Relocations and
   bypasses move *free* tiles, so the total number of free tiles only grows by
   junk heads; `free[Z]` stays positive because
   `(jumps into Z) - (jumps out of Z) ≤ (#rounds where Z's out-edge is dummy) + 2`
   (conservation of the blank's entries/exits, see Run below) and bypasses at
   `Z` are at most `Σ_x (N_Z[x] + 1)`.
5. **Cleanup by double swaps**: with the blank in the last square, a misplaced
   tile of class `Q` is exchanged with a wrong tile inside `Q`, together with an
   exchange of two tiles inside one square (parity), by `exists_double_swap`
   (`6044*n`). Every double swap lowers `misplaced` by at least one.
6. **No Preparation**: corridors start with whatever the (normalized) board
   holds. The blank is first walked into a reservoir (`exists_normalize`), and
   the abstract run starts from `absState` of that board.
7. `k` is even: a column walk crosses a row group of `k` rows by a vertical jump
   of length `k + 1` (odd, so the colours differ).

## Layout (Hub/Basic.lean, Hub/Layout.lean)

Square `Q = (b, c)`: rows `[b*s, (b+1)*s)`, columns `[c*s, (c+1)*s)`. Offsets
`i = row % s`, `j = col % s`.
* `i < k`: row corridor `R(b, i)`. If `c = i` it is the landing strip (region of
  `(b, c)`), else position of the left half (`c < i`) or right half (`c > i`) of
  `R(b, i)`: right half position `q` ↔ column `(i+1)*s + q`, left half ↔ column
  `i*s - 1 - q`.
* `i ≥ k`, `j < k`: if `j = b` own column piece (region), else column corridor
  `C(c, j)`: lower half (bands `> j`) position `q` ↔ band `j + 1 + q/(s-k)`, row
  offset `k + q%(s-k)`; upper half (bands `< j`) ↔ band `j - 1 - q/(s-k)`, row
  offset `s - 1 - q%(s-k)`.
* `i ≥ k`, `j ≥ k`: reservoir (region).
`regionSize = s² - sqCorridor`, `sqCorridor = (k-1)*s + (k-1)*(s-k) ≤ 2ks`.

Insertion positions: `hop1Pos s S h = insPos (hop1Half S h) (hop1Dist S h)`,
`insPos` right `(d+1)s - 1` (source block's column offset `s-1`), left
`(d+1)s - 1 - k` (column offset `k`). `hop2Pos s h D = (|h.1 - D.1| - 1)(s-k)`:
the first cell of the column half inside band `h.1`.

## Module: board operations (`Hub/Simulate.lean`: `simulate_step`)

Given `Rel hd B σ` and `σ.Pre e`, realize `e` with at most `σ.cost s e`
inefficient moves (use `inefficientMoves ≤ length` for everything except the
long corridor walks). Write primitives in new files `Hub/Prim*.lean`.

**hop1 S h y** (`S = (b, J)`, `h = (b, c)`, `J ≠ c`, `H = hop1Half S h`, `p = hop1Pos`):
1. walk the blank inside `h`'s reservoir to `(row offset k, column offset k)`
   (`≤ 2s` moves, only reservoir cells change);
2. vertical jump to the landing strip cell `(offset c, offset j')`,
   `j' = k` if `k - c` is odd, else `k + 1` (crosses rows `c+1..k-1`, restored);
3. straight walk along row `b*s + c` from column `c*s + j'` through the strip
   and on into the half up to position `p` (`exists_line_walk`): positions
   `0..p-1` receive positions `1..p`, the head goes into the strip. Inefficiency:
   strip steps (`≤ s`) plus steps moving a tile of another block column
   (`≤ σ.junkRow H p`); a clean tile moves toward block `c`, i.e. toward its
   target column. (A line-walk lemma counting "steps that move a tile away from
   its target" is the natural tool.)
4. vertical jump from `v` (the cell of position `p`, column offset `s-1` or `k`
   of block `J`) down to `w` = row offset `k`, column offset same or one step
   inward (parity), crossing the other row corridors (restored). `W` → `v`.
5. if `T`'s cell `t ≠ w`, a three-cycle in square `S`'s box on `(v, t, u)`:
   `T → v`, `U → t`, `W → u`, with `u` any other nonblank region cell of `S`.
Result: `Rel C (σ.step s e)`, blank at `w` in `S`'s reservoir, cost
`≤ 2s + 50(k+2) + s + junk + 3022 s ≤ 4000 s + junk` (use `4k+4 ≤ s`).

**hop2 h D y** (`h = (b, c)`, `D = (a, c)`, `b ≠ a`, `V = hop2Half h D`):
1. walk inside `D`'s reservoir to row offset `k` (upper half, `b < a`) or `s-1`
   (lower half), column offset `k` or `k+1` (parity);
2. horizontal jump to the own column piece cell (column offset `a`), crossing
   the column corridors `C(c, a+1..k-1)` at that row;
3. vertical jump across the row group of band `a` (upper: up to band `a-1`, row
   offset `s-1`) or of band `a+1` (lower: down to row offset `k`): length
   `k + 1`, odd. The head (position 0) enters `D`'s own column piece.
4. walk along the column half to position `p`: adjacent steps inside a band,
   vertical jumps (`k+1`) between bands; clean tiles (class `(a,c)`) move toward
   band `a` on adjacent steps (efficient); each crossing costs `≤ 25(k+2)`.
5. horizontal jump from `v` (column offset `a`) into `h`'s reservoir (column
   offset `k` or `k+1`, same row), then three-cycle in `h`'s box placing `X` at `v`.
Cost `≤ 4000 s + 30 k² + junk`.

**jump E Z y** (same band or same block column, `E ≠ Z`): walk inside `E`'s
reservoir to a cell aligned with a reservoir cell `z` of `Z` (same row, resp.
column, parity by choice of `z`'s column/row among two neighbours), jump to `z`
(the tile at `z` goes to `E`), then (if the class-`y` tile is not at `z`) a
three-cycle in a square box containing both squares that swaps the class-`y`
tile into `E` and puts the `z` tile back into `Z`. Cost `≤ 4000 s (1 + sqDist)`.

The effect on `Rel`: only the corridor positions named move; the other
corridor cells are restored by jumps and three-cycles; every region's
multiset of classes changes exactly as `step` says (moves inside one region do
not matter: prove "agrees outside a set `U ⊆ region Q` ⇒ same counts").

## Module: layout facts, Cleanup, Finish (`Hub/Layout.lean` stubs, `Hub/Cleanup.lean`, `Hub/FinishGen.lean`)

* `rel_absState`: corridor cells are not reservoir cells, so they are nonblank.
* `absState_regionTotal`: card of `region Q` is `regionSize`.
* `absState_classTotal`: every cell is exactly one of region / row position /
  column position (a bijection); class `y` has `s²` cells in its target square,
  minus the blank's cell for the last class.
* `misplaced_le_of_rel`: misplaced tiles sit in corridor cells
  (`k² * sqCorridor` of them) or in regions of other squares (`offCount`).
* `exists_normalize`: blank-access walk to a reservoir cell of its square.
* `exists_cleanup`: see simplification 5.
* `exists_finish`: generalize `Algorithm/Finish.lean` (+ `Finish/*`,
  `Partition.square_covers`, `lastGroup`, `Arranged`) from `Dims` to a weaker
  structure (`2 ≤ k`, `8 ≤ side n k`, `k * side n k = n`), keeping the existing
  11/4 development compiling (e.g. provide `Dims → FDims`). Then translate
  `Hub.sqOf`/`classOf` squares to `Partition.square`/`targetGroup`
  (`GroupIndex k = Fin (k*k)` via `finProdFinEquiv`).

## Module: plan and round walk (`Hub/Plan.lean`, `Hub/RoundWalk.lean`)

`exists_rounds`: dummy matrix with row sums `(recv - sends)⁺`, column sums
`(sends - recv)⁺` (transportation: induction on the total), loops
`Δ0 - max(sends, recv)` with `Δ0 = max_S max(sends S, recv S)`; the sum
`A = T + dummy + loops` has all row and column sums `Δ0`; Hall
(`Finset.all_card_le_biUnion_card_iff_exists_injective`) gives a permutation in
the support; subtract and recurse. Label, for each `(S, D)`, the first `T S D`
rounds using `S → D` as real and the rest as dummy.

`exists_round_events`: phase 1: for each square `Z` (snake order) whose edge is
dummy and whose in-edge is real, relocate to `Z` and walk `Z, perm⁻¹ Z, …`
while the in-edge is real and the square is unserved. Phase 2: for each square
in snake order that is unserved with a real in-edge, relocate there and walk
until the cycle closes (all edges on it are real). Prove: each real edge is
served exactly once; phase-2 walks end where they start; relocation weights
`≤ 2k` in phase 1 (one per dummy edge), and in phase 2 they telescope along the
snake order (`sqDist P Q ≤ |snake P - snake Q|`).

## Module: in-flight bound (`Hub/InFlight.lean`: `exists_good_order`)

Per half `H` and distance `d` (the source at distance `d` is one square, so a
round inserts at most once per `(H, d)`): `G_d(i) ∈ {0,1}`, `a_{x,d}(i) ∈ {0,1}`,
`B_d = Σ_{d' ≥ d} G_{d'}` (totals over the `Δ` plan rounds), window
`w_d = min Δ ⌈2(p_d+1)Δ/B_d⌉`, `λ = 7 (log₂ n + 1)`.
1. Maclaurin (`e_w(y)/C(N,w) ≤ (Σ y/N)^w` for `y ≥ 0`, by smoothing: replace
   `y_i > m > y_j` by `m, y_i + y_j - m`) ⇒ for a uniform `w`-subset `W`,
   `E Π_{j∈W} y_j ≤ (mean y)^w`.
2. Tails: `#{W : Σ_W g < μ/2} ≤ C(N,w) exp(-(1/2 - 1/e) μ / K)` for
   `g ∈ [0, K]` (take `y = exp(-g/K)`), and `#{W : Σ_W a ≥ 2μ + λ} ≤ C(N,w) 2^(-λ)`
   for `a ∈ {0,1}` (take `y = 2^a`); `μ = w Σ/N`.
3. `σ ↦ σ '' T` is `w!(Δ-w)!`-to-one onto `w`-subsets: permutation counts.
4. Union bound over `≤ 2k² · k · (k+1) · Δ` window events ⇒ a good `σ` exists
   (`s ≥ 64 k (log₂ n + 1)`, `p_d + 1 ≥ s - k`).
5. Push lemma and windows (deterministic): a tile inserted in round `τ0` at
   `p_d` is gone after `p_d + 1` insertions at positions `≥ p_d`; with the
   window property it is gone by the end of round `τ0 + w_d`; so present
   `(x, d)` tiles ≤ rounds in `[τ - w_d, τ]` inserting `(x,d)` ≤ `2A(w_d+1)/Δ + λ`.
6. Sum: `Σ_d G_d / B_d ≤ H(B_0) ≤ 1 + ln(kΔ)` (harmonic numbers), total per hub
   `≤ 4n(1 + ln(kΔ)) + 8k + 2k²λ ≤ Rhub n`.

## Module: the run (`Hub/Run.lean`: `exists_valid_run`)

Ghost state on top of `IState`: roles `sched stock free home : Sq k → Sq k → ℕ`
with `cnt = sched + stock + free + home`, ghost rows `Ghost k`, counters
`out`, `byp`, and bookkeeping for the blank's jumps in/out per square.

Construction: `T S D = σ0.cnt S D` (`S ≠ D`), `exists_rounds`, set aside the
first `Q' = min Δ0 (Rhub n + 8 k s + 10)` rounds (their real edges' tiles and
`min(home0, Q')` home tiles start as `free`), plan rounds `rs i = rs0 (Q' + i)`,
`σ` from `exists_good_order`, high-level events = concatenation over `τ` of
`exists_round_events (rs (σ τ)) cur`, resolved as in the file header.

Invariants/facts to prove:
* `recv - sends = sqCorridor - corrCount + [blank] - [last]` from F1, F2, so
  dummy out-edges `≤ 2ks + 1` per square and `≤ k²(2ks+1)` in total; loops
  `≤ home0 + 2ks + 2`, so `free0 ≥ Q' - 4ks - 3`; `Δ0 ≤ s² + 1`.
* stock identity (PROOF.md Lemma 1): `stock h x = out h x - new h x + byp h x`
  for `x.2 = h.2`, `x ≠ h`; a bypass happens only at `stock = 0`, so
  `byp h x ≤ N h x + 1` with `N` from `exists_good_order` (the insertion list of
  the run is `Consistent` by construction).
* free lower bound: `free Z ≥ free0 Z - (jumps into Z - jumps out of Z) - bypasses at Z`;
  jumps in − out `≤` (#rounds so far where Z's edge is dummy) + 2, from: entries −
  exits of the blank into `Z` is `0` or `±1`, serves move the blank `D → S`,
  and per round `Z` sends at most once and is served at most once.
* validity: `sched ≥ 1` for the edge being served, `stock ≥ 1` in case (iii),
  `free ≥ 1` for bypasses/relocations.
* cost: hops `≤ 2 n²` of them; `Σ junk ≤ Φ₀ = Σ (junk positions q + 1) ≤ 2k²n²`
  (inserted tiles are clean, so `Φ` only decreases); bypasses
  `≤ k²(Rhub + k)`, each `≤ 4000 s (1 + k)`; relocation weights per round from
  `exists_round_events`, each weight unit `≤ 8000 s`.
* end: all plan edges served, so `sched = 0`; `offCount ≤ Σ stock + Σ free`
  `≤ (k² n + Σ byp) + (Σ free0 + junk heads)`.

## Module: asymptotics (`Hub/Main.lean`)

Choose `k` even with `k ≈ (n / (128 (log₂ n + 1)))^(1/3)` (so that
`64 k (log₂ n + 1) ≤ s = ⌊n/k⌋` and `4k+4 ≤ s`), apply
`exists_hub_solution` to the residual `k*s` board after the Parberry prefix
(`Algorithm/GeneralSize.lean`), and bound `hubBound + prefix` by
`C n^(8/3) (log n)^(1/3)`. Generalize `UniformApproximation` /
`Proposition9.lean` to an error function `f ≥ n²` eventually.
