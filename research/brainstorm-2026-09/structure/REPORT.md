# Global-structure ideas for the Transport/corridor bound (current 8.45 n^(11/4))

Scripts (run with `uv run --with numpy --with scipy python <file>`):
`game2.py` (reproduces the notes' look-ahead game: 2.5 for e=4 and 3.0 for e=5), `opt.py` (rectangles and V density),
`amort.py`, `restore.py`, `percell.py` (budget/amortized bounds).

Notation: constant = (4/3) A^(3/4) (3P)^(1/4), with A = 3.5 (Transport) and P = 12.5 (Preparation 11.5 + Arrangement 1).
One unit of A is worth about 1.8–1.9 in the constant, and one unit of P about 0.14–0.17.

## Ranking

| # | Idea | New A / P | Constant | Exponent | Lean effort |
|---|------|-----------|---------:|----------|-------------|
| 1 | **Exit-and-restore + per-cell charging** | A 3.5 -> 2.75 | **~7.05** | same | moderate |
| 2 | (1) + vertical carry for same-band sources | A -> ~2.65 | ~6.85 | same | moderate+ |
| 3 | Rectangular groups / 2 V-columns per group per square | small | 8.34 (or 7.00 on top of 1) | same | large, not worth it |
| 4 | Shared vertical corridors per target band (k^2 n cells) | — | — | would give 8/3, **but broken** | — |
| 5 | Dimension-by-dimension / recursive halving / bulk conveyors | — | — | n^3 on the rotation | — |

## 1. Exit-and-restore, with a per-cell potential in place of per-transfer look-ahead  (main recommendation)

**Observation.** The three-row carry (`Moves/ShiftCarry.lean`, `pairsEffect`) moves T from `(2, m+1)` to `(1, 1)`.
Its only other effect is that T's row segment `[1..m]` shifts one cell *away* from the corridor, and the tile at
`(1,1)` drops into `(2,1)`. After T has gone into the corridor, the blank is back near `(1,1)`. Step down to `(2,1)`
(this restores the dropped tile) and walk right along row 2 to `(2, m+1)`. Each step moves a row-2 tile back one
cell. **The reservoir is then exactly restored, except that T is gone and the blank sits on T's original cell.**
Cost: the length grows from 6m to about 7m, but the net displacement is T's alone (about m). So
`2·ineff ≤ 7m + m`, i.e. still **≤ 4m inefficient moves** (3m if T moves toward its own square).
In the worst case the walk-back is free, because it undoes the carry's damage.

**Consequence.** The whole Transport now changes reservoir tiles in only three ways:
- vertical slides of the blank's column (the entry "reservoir slide");
- removal of the extracted T;
- insertion of a delivered tile of the reservoir's own group, in the blank's column.

So **no off-diagonal tile ever changes column** (up to O(1) cells per transfer next to the corridor).
- Every extracted tile is an original off-diagonal tile. This holds because `TransportCounts.move` only moves `(j,i) -> (i,i)`.
- Correct tiles are never extracted.

**Charging.** Charge each extracted tile T, sitting at column x and row r of its reservoir:
- its own exit, `4·min(x, s-x)` (nearest side; look-ahead is no longer needed);
- the *next* transfer's in-square horizontal travel. The blank starts at column x, so this is `x`, `s-x`, or `|x-v'|`, all ≤ `max(x, s-x)`;
- vertical: the next entry is at most `max(r, s-r)`. A same-band source T' at row r' adds the in-band V descent, and
  `min(r+r', 2s-r-r') ≤ max(r,s-r) + min(r',s-r')`. So each tile's total vertical charge is ≤ s.

So `f(x) = 4·min(x,s-x) + max(x,s-x) + s`. Its worst value is 3.5s, the same as today's per-transfer bound. But
the potential is `Φ(B) = Σ over reservoir cells holding an off-diagonal tile of f(column)`. It starts at most at
`Σ over all reservoir cells of f = (1.75 + 1)·k²s³`, and each transfer decreases it by at least that transfer's
cost minus O(k²). **A = 2.75**, which is attained when every tile is wrong, e.g. the 90° rotation.

Numerical check (`restore.py`): the budgeted mean-payoff game gives 1.745 for the exit+horizontal part. That
matches the closed form 1.75. Same-strip-only boards are the binding case. So using `e=3` toward T's own square
does not improve the worst case: 1.745 for e=3 and for e=4. Balancing: `c = (2A/75)^(1/4) ≈ 0.52`,
constant `(4/3)·2.75^(3/4)·37.5^(1/4) ≈ 7.05`.

**Why this is not what the notes already rule out.** The notes state that the look-ahead game value of 2.5s is
optimal *per transfer*. That is a statement about adversarial tile positions at each step. Here the positions are
budgeted: each reservoir cell supplies at most one extraction, and without the restoring walk that budget is
invalid. Without the walk, the carry pushes the wrong tiles in front of T one cell deeper. With deepest-first
extraction, an adversary then gets 2s per extraction again (see the analysis in `amort.py`: pushing-drift ruins
amortization; the naive budget bound 2.02 is not sound without restoring).

**Formalization sketch.**
1. A new strip word `pairs ++ walkBack` with trace `= swap blank/T` on `ℕ×ℕ`. This reuses `StripTrace` and
   `manhattan_le_of_displacement`, and should be a small extension of `ShiftCarry.lean`.
2. The exit core ends with the blank at T's cell, not next to the corridor.
3. Replace `transferPotential` (Ψ, which depends on the next source) with the board potential Φ above. The needed
   facts:
   - the reservoir slide permutes cells inside one column;
   - the entry jump inserts an own-group tile in that column;
   - the exit removes T and restores everything else.
   `exists_path_of_count_run_amortized` already telescopes a potential, so only the potential's type changes (it now depends on the board).
4. Transport's total becomes `Φ(start) ≤ 2.75·k²s³ + O(k s³)`. The bound `≤ n²` transfers × per-transfer bound is no longer needed.

The look-ahead proof (`Chooses.unique`, the 10s + 2Ψ case analysis) could be deleted. Risk: the O(1) boundary
cells near the corridor, and the jump into the corridor. Both only add O(k²) per transfer, which is lower order.

## 2. Vertical exit for same-band sources (optional, about −0.2)
For a source in the same band, H_i passes directly above or below the source reservoir. So T' can be carried
*vertically* into H_i: cost `4·min(r', s-r')` plus the restoring walk. This needs no V descent and no horizontal
exit. Taking the minimum over the two routes lowers the average source charge (`percell.py`): A ≈ 2.645,
constant ≈ 6.85. It needs a vertical variant of the exit core, and handling of the corridor rows between the
reservoir and H_i. Do this only after idea 1.

## 3. Decoupling the geometry (rectangles, corridor density)
Generalize to groups of size s_v × s_h and m V-columns per group per square (spacing w = s_h/m).
- Transport ≈ n²(s_v + γ(m)·s_h), where γ is the look-ahead game value: γ = 2.5, 1.74, 1.5, 1.37 for m = 1, 2, 3, 4.
- Corridor cost ≈ P·n^5·m/(s_v s_h²).

Optimizing (`opt.py`) gives: squares with m=2 → 8.36; rectangles with m=1 → 8.41; rectangles with m=2 → **8.34**.
On top of idea 1 (per-tile charge `s_v + 0.75 s_h + w`), AM-GM gives `4(0.75·P)^(1/4) ≈ 7.00` against 7.05.
The own-square costs, entry (≈ s_v) and in-square travel (≈ s_h), do not shrink with corridor density. So these
knobs are worth at most about 1%, and each one changes `Partition`/`Dims`. Not recommended.

## 4. Can the exponent move? (skeptical assessment)
- **Where 11/4 comes from.** A chain shift is efficient only if every corridor tile wants to move toward the
  blank's start. The chain must also deliver a tile of the *specific* destination group. So each group needs its
  own corridor within distance s of every reservoir cell: k²·k·n = n^4/s³ cells, each filled over a distance of
  about n. The local costs of each transfer are Θ(s):
  - moving home tiles blindly inside the start square;
  - the exit from a reservoir of side s.

  Hence n^5/s³ + n²s, minimized at s = n^(3/4). More levels (Zhong's Finish recursion) only act *after* the first
  level, whose cost already has this form. Denser corridors (idea 3) lower the exit cost but not the own-square costs.
- **Shared vertical corridors per target band** would need only k²n cells, giving k²n² + n³/k and hence
  **n^(8/3)**. They fail at the junction with H_i: the tile that enters H_i must be of group i.
  - A jump that pulls the nearest group-i tile out of the shared column depletes that column. Repeated
    requests for one group push the depth to about min(D, #requests·k), which can be Θ(n) per transfer.
  - Letting foreign same-band tiles into H_i costs about n in blind horizontal travel each.

  I see no repair. It is still the most interesting open direction if someone wants to attack the exponent.
- **Dimension-by-dimension routing (horizontal, vertical, horizontal) and recursive halving.** Both would need
  monotone routing, and it is infeasible on the 90° rotation. Counting argument: band 0, strip k−1 would have to
  receive s² tiles of each of the k band-classes. For halving, the quadrants form the 4-cycle
  TL→TR→BR→BL. Pairwise swaps between halves move tiles about n/2 away from their targets, which is Θ(n³).
  Zhong's n×2 O(n log n) divide-and-conquer does not carry over.
- **Bulk conveyors** cost about 0.5 inefficient moves per tile per cell, even when moving toward targets. So they
  are Θ(n³) over long distances, and only help locally, below about 7s.
- **Literature.** Zhong (IJTCS-FAW 2023, LNCS 13933) is the source of O(n^2.75), and searches found no follow-up
  that improves it. The easy lower bound on OPT − M is Ω(n²) (linear-conflict type, e.g. reflected rows). The gap
  between n² and n^2.75 appears open. Improving the exponent would be a research result, not a tuning step.

## Bottom line
The architecture of the paper is near its constant-level limits in everything except **how Transport is
accounted for**. Restoring the reservoir after each exit, and charging the extraction cost to reservoir cells
instead of to adversarial per-step positions, lowers A from 3.5 to 2.75. That takes the headline constant from
**8.45 to about 7.05**, the largest single gain available here, and it makes the look-ahead proof unnecessary.
After that, P matters relatively more: at A = 2.75, one unit of P is worth about 0.14 and one unit of A about 1.9.
