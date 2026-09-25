# Redesigning Preparation (and Arrangement)

Halved coefficients in units of k⁵s²; constant K(P) = min_c (A/c + P·c³), A = 3.5
at the time of writing. The constraint `s ≥ k³` (c ≤ 1) comes only from the current
staging area. Scripts: consts.py, conveyor.py, drain.py. Nothing formalized.

| Design | P | K (c ≤ 1) | K (c free) | effort | risk |
|---|---|---|---|---|---|
| current | 12.5 | 8.44 | 8.44 | – | – |
| A: Arrangement as a drain run | 11.5 | 8.27 | 8.27 | moderate | low |
| E: current Preparation charged by displacement | ≈10.5 | ≈8.08 | ≈8.08 | moderate | low |
| B: conveyor-family Preparation + current Arrangement | 7/3 | 5.55 | 5.55 | high | low–med |
| B + Arrangement sideways conveyor | 5/3 | 5.10 | 5.10 | high | low–med |
| **B + A** | **4/3** | **4.82** (c≈0.97) | 4.82 | high | low–med |
| C: no Preparation, Transport flushes dirty corridors, + A | ≈2/3 | 4.17 | 4.06 | very high | medium |
| D: adaptive corridors filled from beyond, + A | ≈1/3 | 3.83 | 3.41 | very high | high |

(With exit-and-restore, A = 2.75, B + A gives ≈ 4.0.)

## Key facts
1. Only long-distance moves matter: k⁴s vertical-corridor cells; horizontal ones 2k³s
   (lower order); anything O(s) per corridor tile totals O(k⁴s²), lower order.
2. Σ over pairs of squares of distance = 2k²(k³−k)/3 → (2/3)k⁵ (exact).
3. Transport's and Preparation's worst cases coincide: a neighbour derangement σ (each group
   in a square next to its own) makes every tile off-diagonal and makes corridor filling raise
   M by (2/3)k⁵s² − O(k⁴s²). No trade-off between the phases.
4. Lower bound (fixed architecture, corridors full before Transport, Preparation does not
   sort reservoirs): P_prep ≥ 2/3. Not rigorous for arbitrary paths (sorting reservoirs at
   the same time could lower M by ~n²s, same order as k²s³).
5. Conveyors cost 2 moves per useful tile-cell (2mD+3D for m tiles over D cells); displaced
   tiles move a net m·D with adversarial sign, so (length+ΔM)/2 gains nothing over length.
   Only Transport's chain slide makes just the blank flow back.

## A. Arrangement as a drain run (do first)
- After Transport: reservoirs sorted, corridors full. Step x → z: blank from reservoir of x
  along H_x and group x's vertical line to the far end of V(z,x); pulls in the reservoir
  tile of z next to the corridor block (group z, already home); chain shifts one step toward
  x, delivering one group-x tile into x's reservoir. = Transport transfer with exit distance 0.
- Cost per step: entry ≤ s, horizontal within start square ≤ s, re-sliding tiles already fed
  ≤ s, jumps O(k²); every other slide moves a group-x tile toward x (free). k⁴s steps →
  ~3k⁴s², lower order. Arrangement coefficient 1 → 0. End state: every tile in its square.
- Ordering: the chain behind each step must still be group x. Drain in rounds by band
  distance d = k−1 down to 0, H_x cells last. Each round balanced (out-degree = in-degree
  = k·s·|{b±d}∩[0,k)|). Greedy walk only gets stuck at its start; moving the blank costs O(n)
  and exhausts one square → ≤ k² moves per round, O(k³n) total. drain.py confirms balance.
  The count run's minimum-source/LastInvariant device does not carry over; this relocation
  argument replaces it.
- Formalization: reuse entry, horizontal, capped vertical route, exit/jump lemmas with exit
  distance 0; new run argument (rounds, balance, blank moves); charge by inefficiency
  directly; `arrangement_manhattan` and FamilySwap Arrangement no longer needed.

## B. Preparation by long-range conveyor families
1. Assignment: choose which source square y supplies each of the k⁴ families of s tiles for
   V(i,j). Proportional plan (y gives i the share of group j that y holds) costs ≤ (2/3)k⁵s²
   tile-cells since every square holds s² tiles; an integer optimal plan is no worse and has
   ≤ 2k² pieces per group (overhead O(k⁵s)).
2. Gather: in each source square, gather outgoing tiles into column segments at O(s) per tile
   (e.g. Parberry prefix embedded in a square). Do NOT solve whole squares (k²s³ total).
3. Vertical leg: column conveyor along a dedicated lane of two reservoir columns (touches only
   reservoir cells and H rows).
4. Turn: at band(i)'s H rows convert column → row, O(s²) per family.
5. Horizontal leg: row conveyor along two H rows of band(i) (`exists_conveyor` exists).
6. Park in square i, place families into the V block with protected local moves.
7. Refill H rows last (lower order); re-stage the spare tiles needed for count-run margins.
Displaced tiles only scramble lane/H cells and move reservoir tiles between reservoirs;
Transport only reads counts. Coefficient: 2 moves per tile-cell × (2/3)k⁵s² → length
(4/3)k⁵s²; charged at full length P_prep = 4/3 (within ×2 of the 2/3 bound).
Risks: lower-order local lemmas (gather, turn, park, place) must stay O(s) per tile with
disjoint zones. Effort ≈ current Preparation (~1.1k lines) + local placement infrastructure.
Stretch "B-loops": dense loops with families both ways could approach 1 move/tile-cell
(P ≈ 2/3, K ≈ 4.17); recursive halving has balanced midline flows, but a plain 2×2w loop
rotated by w still costs 2 per useful tile-cell; making all four quarters useful is open.

## C. No Preparation: Transport tolerates dirty corridors
Prefill only H rows and same-band vertical corridors (lower order, must be clean). Cross-band
lines start with garbage, pushed by each transfer toward the junction, along H_x into x's
reservoir, becoming ordinary misplaced tiles; lines fill with group x; drain as in A. Each
garbage tile costs ≤ its route length d(z,x)·s, total (2/3)k⁵s² → P ≈ 2/3 (sideways ejection
≈ 1/3 but adversary can deny a local replacement). `Clear` → "routes used are clean";
garbage breaks count-run Margins → one run over all misplaced tiles incl. corridor tiles.
Effectively rewrites Transport's formal core.

## D. Adaptive corridors filled from beyond
A line of group x (column, direction) is needed down to square z only if group-x reservoir
tiles remain at or beyond z (columns c and c−1, for the right exit). Fill it from those tiles
(moving toward band(x): efficient). Too few → absorb into nearest corridors, drain later
(strays < k³s). Unneeded corridor cells become reservoir. Worst case supply only at extreme
band: ≈ k⁵s²/3 tile-cells (0.27 at k=16 → 1/3); filling ≈ 1 per tile-cell → P ≈ 1/3; dropping
s ≥ k³ gives c ≈ 1.37, K ≈ 3.41. Same unified-run problem as C; needs both exit columns;
no known filling mechanism at 1 per tile-cell without damaging neighbouring lines.

## Other
- E (current Preparation by displacement): K ≈ 8.1–8.3, dominated by B.
- Arrangement sideways conveyor: 1 → 1/3, superseded by A.
- Recursive halving: Preparation spreads groups (opposite of sorting), ≥ 2/3; only useful as
  scheduling for B-loops.
- Geometry: any route needs one group-specific leg per (group, band) or (group, column):
  k⁴s cells, so k⁵s² is structural; sharing lines between groups fails at junctions.
