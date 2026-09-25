# Conveyor Preparation: design

Status: design only, nothing formalized. Branch `conveyor-preparation`, off `main` at
`794051f` (constant 7.08).

Goal: replace Phase I (Preparation, `11.5*k⁵s²` inefficient moves) by a construction
costing `(4/3)*k⁵s² + O(k*s³)`. With Transport `A = 2.75` and Arrangement `1`, the
constant `(4/3)*A^(3/4)*(3P)^(1/4)` drops from `7.05` (P = 12.5) to about `4.6`
(P = 7/3); with the drain Arrangement as well (P = 4/3), to about `4.0`.

Background: `research/brainstorm-2026-09/prep/REPORT.md` (design B). This document
fixes the geometry and the order of operations, and lists the lemmas.

## 1. What Preparation must produce

`Prepared hk B` (`PhaseStates.lean`) = reachable, `Clear` (every `H_i` cell holds a
group-`i` tile, every `V(i,j)` cell a group-`j` tile) and `LastRepresentatives` (the
last reservoir holds a tile of every other group). Reservoir contents are otherwise
free: Transport reads only counts.

Layout B (`Partition.lean`), `n = k*s`, `m = s - 2k`:

- band `r`: rows `[r*s, (r+1)*s)`; its first `2k` rows are horizontal corridor rows;
- `V(i,j)`: column `gc(i)*s + j` of square `i`, rows `[gr(i)*s + 2k, (gr(i)+1)*s)`;
  the `k²` corridors of square `i` form its **V block**, columns `[gc*s, gc*s + k²)`;
- reservoir `i`: rows `[gr*s + 2k, (gr+1)*s)`, columns `[gc*s + k², (gc+1)*s)`.

Only the V blocks matter at leading order: `k⁴*m ≈ k³n` tiles that travel `Θ(n)` on
average. H rows are `2k²n = 2k³s` tiles; anything `O(n)` per H tile is
`O(k⁴s²)`, lower order.

## 2. Cost model

- A tile needed in `V(x,j)` may be any group-`j` tile. With `c_j(y)` the number
  of group-`j` tiles in square `y`, the **proportional plan** takes
  `a(y,x,j) ≈ m*c_j(y)/s²` tiles from `y`. Every square then sends about `m`
  tiles to every square, and the tile-distance is
  `m*s*∑_{x,y} d(x,y) = (2/3)*k⁵s² + O(k⁴s²)` in square units (`Arrangement/Cost.lean`
  already has `3*∑|a-b| = k³-k`).
- **Conveyor** (`Moves/Conveyor.lean`, `exists_conveyor`): a segment of `f` tiles
  moves one cell along its own line in `2f+3` moves, the blank returning along an
  adjacent lane line. Non-segment tiles only circulate between the segment line
  and the lane (ahead of the segment into the lane, back out behind it), so **a
  pair of lane lines is sealed**: lane tiles stay in the lane pair.
- Charged at full length (`ineff ≤ length`): `2 * (2/3)k⁵s² = (4/3)k⁵s²`.
  Charging by displacement could give about `1`, but the displaced lane tiles
  move with adversarial sign; not planned.
- Per-family overheads are harmless: with at most `k⁶` families (one per
  `(y, x, j)`), `O(s)` per family is `k⁶s ≤ k³s²`, and the conveyor's `+3` per cell
  is `3k⁶n = 3k⁷s ≤ 3k⁴s²` (uses `s ≥ k³`). Per-tile overheads of `O(s)`
  (gathering, turning, placing) total `O(k⁴s²)`. Turning a family of `f` tiles
  costs `O(f²)`; `∑ f² ≤ m * ∑ f = O(k⁴s²)`.

## 3. Geometry: lanes and regions

In every square `y = (ry, cy)`:

- **lane columns**: the last two columns, `cy*s + s-2` and `cy*s + s-1`, full band
  height. Stacked over the bands they form one vertical lane per column of
  squares. They are reservoir columns and H-row cells: no constraint during the
  phase except at the end (H cells refilled; reservoir cells free).
- **lane rows**: the first two rows of each band, `ry*s` and `ry*s+1` (H rows).
  Across the band they form one horizontal lane.
- **region** `R(y)`: rows `[ry*s + 2, (ry+1)*s)` × columns `[cy*s, cy*s + s-2)`, a
  rectangle; it contains the V block, the reservoir minus lanes, and the non-lane
  H rows of square `y`.

Traffic moves only in lanes; local work stays inside one region. A tile starting in
`R(y)` stays in `R(y)` until its family ships (the only moves touching `R(y)` are
`y`'s own extractions and placements into `y`).

**Supply.** Only tiles starting in `S(y) = R(y) ∖ (H rows)` (V block and reservoir
minus lanes) are planned. The adversary can hide at most the non-supply cells,
`k²(2ks + 2s)` over the board, of one group, so the supply of every group is at
least `s² - 2k³s - 2k²s`. The plan needs `k²m + k⁴` per group, so
**`s ≥ 3k³` suffices** (check small `k`). This means strengthening `Dims` from
`k³ ≤ s` to `3k³ ≤ s` (or requiring it only in Preparation). Both actual uses
satisfy it: `GeneralSize` (`c = 2/3`) has `s/k³ ≈ 1/c⁴ ≈ 5`, `TwoLevel`
(`c = 6/11`) has `≈ 11`. The paper's exact case `n = k⁴, s = k³` would be lost;
it's only mentioned in comments.

Alternative if the stronger `Dims` is unwelcome: add the non-lane H rows to the
supply (then only lanes are hidden: `4k²s` cells, `s ≥ 5k²` suffices, true for
`k ≥ 5` from `s ≥ k³`; small `k` separately). This costs a slightly more
complicated extraction workspace.

## 4. The plan (tile identities fixed up front)

For each destination square `x`, group `j`, and source `y`:
`a(y,x,j) = ⌊m*c'_j(y)/|S(y)|⌋` where `c'_j(y)` counts group `j` in `S(y)`.

- Supply: `∑_x a(y,x,j) ≤ k²m*c'_j(y)/|S(y)| ≤ c'_j(y)` since `k²m ≤ |S(y)|`.
- Deficit `r(x,j) = m - ∑_y a(y,x,j) ≤ k²`-ish rounding plus the imbalance of
  `∑_y c'_j(y)/|S(y)|` versus `1`. **Check this carefully:** `∑_y c'_j(y)/|S(y)|`
  equals `1` only if the hidden cells hold exactly their share of group `j`; in
  general the deficit is `O(hidden cells of group j)/k²`-ish per corridor. The
  deficits are filled by extra families from any square with spare group-`j`
  supply. Their tile-distance is at most `2n` each and must total `O(k⁴s²)`: the
  total deficit must be `O(k³s)`. The rounding part is `≤ k⁶ ≤ k³s`. The
  imbalance part needs a real estimate: a first job for the simulation.
- Cost bound: `∑ a(y,x,j) d(y,x) ≤ m ∑_{x,y} d(y,x)` because
  `∑_j c'_j(y)/|S(y)| = 1`.

Formal plan: choose, per `(y,x,j)`, a `Finset` of specific tiles of `S(y)`, pairwise
disjoint, with the stated cardinalities (greedy by an arbitrary order of `S(y)`'s
cells). A family is identified by its tiles; later lemmas track tiles, not cells.

Simpler alternative worth checking first: the König/Hall decomposition of the
almost-regular count matrix gives exact integer blocks (`m` tiles from every `y` to
every `x`, `m` of each group into every `x`), with no deficits. Hall is in mathlib
(`Finset.all_card_le_biUnion_card_iff_exists_injective`); peeling perfect matchings
off a `d`-regular bipartite multigraph is maybe 200 lines. Needs the hidden cells
handled (they break regularity), probably by planning with all cells and
pre-moving hidden supply. The rounding approach is probably easier.

## 5. Order of operations

Process destinations `x` in any order; for each `x`, groups `j = 0, …, k²-1`; for
each `(x, j)`, the families `F(y,x,j)` over all sources `y`; for each family:

1. **Extract** in `R(y)`: bring the family's tiles into lane column `cy*s+s-2` as a
   contiguous column segment inside band `ry`. Workspace: the rectangle of `R(y)`
   right of the V block if `y`'s V block is already filled, otherwise all of
   `R(y)`. Both are rectangles adjacent to the lane. Cost `O(s)` per tile.
2. **Vertical conveyor** along the lane pair of column-of-squares `cy` from band
   `ry` to band `rx`, crossing other bands' H rows (lane cells only). Transpose of
   `exists_conveyor`.
3. **Turn** at band `rx`: the column segment becomes a row segment in lane row
   `rx*s+1`. Local, in lane columns ∪ lane rows of square `(rx, cy)` plus whatever
   workspace is needed (see §7, the main local risk). Cost `O(f²)`.
4. **Horizontal conveyor** along lane rows `rx*s`, `rx*s+1` from column-of-squares
   `cy` to `cx`.
5. **Place** into `V(x,j)`: turn back down into `R(x)` and put the family's tiles
   into the next free cells of column `j` of `x`'s V block. Invariant: V columns
   `< j` of `x` are full, column `j` is filled from the bottom. So the free
   workspace is a rectangle whose first column is partly solved, the shape of
   Parberry column solving (`Parberry/LeftPlacement.lean`, `ColumnSolve.lean`,
   `RectPlacement.lean`). Cost `O(s)` per tile.

Families with `(ry, cy) = (rx, cx)` skip 2–4; same band skips 2; same column
skips 4 (turn only if needed).

After all V blocks are full:

6. **H rows.** Fill the `2k` H rows of every band, lane rows included, from supply
   in the reservoirs, protecting the V blocks. `O(n)` per tile, lower order. Open:
   the last two H rows of a band sit on V block cells in `k²` columns per square,
   so filling them needs a 2-row strip technique there (`Zhong/Algorithm/Strip2`?)
   or a different fill order (e.g. fill H rows from the bottom one up using the
   band above's reservoir rows, which are V-free outside the V block columns).
   The current `Preparation/Horizontal.lean` fills H rows before any vertical
   work, so it cannot be reused as is: the horizontal lane must be H rows (every
   other row crosses V blocks), so H rows can only be filled after the traffic
   ends. Needs a design pass.
7. **Representatives.** Put one tile of each other group into the last reservoir,
   `O(n)` per group (`Preparation/Representatives.lean` has the geometry today).

## 6. Accounting targets

| Step | Leading cost |
| --- | --- |
| Vertical conveyors | `2 * vertical tile-distance` |
| Horizontal conveyors | `2 * horizontal tile-distance` |
| together | `2 * (2/3)k⁵s² = (4/3)k⁵s²` |
| Extract, turn, place, per-family overheads, deficits | `O(k⁴s²)` |
| H rows, representatives | `O(k⁴s²)` |

Budget in `Admissible` (quadrupled): Preparation `⟨0, 6, R⟩` if the bound is
`4*ineff ≤ (16/3)k⁵s² + …`; `16/3` is not an integer, so bound it by `6` (length
`(3/2)k⁵s²`, P_prep = 1.5) or bound `3*4*ineff`. Decide when the arithmetic is in
hand. Then rebalance `c` in `TwoLevel` (the minimizer moves up, roughly
`c ≈ (11/(3*4*P'))^(1/4)`) and in `GeneralSize`.

## 7. Risks, in order

1. **Local lemmas with protection** (extract, turn, place): Parberry placement
   lemmas exist for rectangles; the turn needs a workspace that is not someone
   else's data. The candidate workspace for the turn is the lane rows and columns
   of square `(rx, cy)` plus its non-lane H rows (free until step 6). A
   `2k`-high strip is enough to place a row segment of length `f ≤ m` from a
   column segment fed into it by conveyor steps, a few tiles at a time. Needs a
   loop lemma.
2. **H-row fill with V blocks protected** (§5 step 6).
3. **Plan deficits** (§4): must be `O(k³s)` in the worst case.
4. **Bookkeeping**: a phase invariant per stage (which cells are final, which
   tiles are still in which region, lane contents arbitrary). Probably one
   `structure` with `R(y)`-membership of unshipped planned tiles, full/partial V
   columns, and "everything else free".
5. **Parity/blank position** between steps: blank access paths (`Moves/BlankAccess.lean`)
   at `O(n)` per family, total `k⁶n`: fine.

## 8. Work plan

0. Simulation (`uv run`): random and adversarial boards (neighbour derangement,
   everything of a group hidden in lanes/H rows) at `k = 3..6`. Measure plan
   deficits and the exact move count of steps 1–5 with simple local routines;
   confirm `(4/3)k⁵s²` plus a small lower-order term.
1. Settle §5 step 6 (H rows) and the turn workspace on paper.
2. Lean, bottom-up:
   a. column conveyor (transpose of `exists_conveyor`), lane-sealed effect;
   b. multi-cell conveyor runs with tile tracking (`exists_conveyor` covers runs
      along a row already; check its stated effect suffices);
   c. extract and place (Parberry-based, protected rectangle);
   d. turn;
   e. family shipment = a–d composed, with its cost and effect;
   f. plan (`Finset`s of tiles) and the cost sum `≤ m*∑ d(y,x)`;
   g. the phase loop over `(x, j, y)` with the invariant;
   h. H rows and representatives;
   i. `Admissible`, `GeneralSize`, `TwoLevel` arithmetic; `Dims` change.
3. Delete the old Preparation (staging, `MixedStaging`, `Preparation/Vertical`,
   probably `Preparation/Horizontal` unless reused in step 6).

Size guess: 3000–5000 lines. a, b and d are also what the Arrangement sideways-leg
improvement (1 → 1/3) needs, so they are useful even if the redesign stalls.
