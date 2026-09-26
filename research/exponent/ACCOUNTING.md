# Cost accounting for two-hop transport in Euler rounds

Status: historical draft, superseded by `PROOF.md` (own-sender pairing, bypasses and a
random round order instead of the three conditional lemmas below) and its formalization
(`LEAN_PLAN.md`). The lemmas it leaves open were resolved there, at the price of a
`(log n)^(1/3)` factor.

Pen-and-paper. Goal: every term O(n^(8/3)) at k = n^(1/3), s = n/k = k^2, conditional on the
lemmas listed at the end. All costs are inefficient moves (length minus Manhattan decrease,
up to the factor 2 of `length + M(end) = M(start) + 2*ineff`).

## Layout

k x k squares of side s. Square (a,c) = band a, column block c.
- Row R(b,c): one board row inside band b, for each target column block c (k rows per band).
  Holds tiles whose target column block is c (any target band). Two halves: left of block c
  and right of block c; the head of each half is at the edge of block c.
- Column C(c,a): one board column inside column block c, for each target band a (k columns
  per block). Holds exactly class (a,c). Two halves: above and below band a.
- Hub (b,c): the reservoir of square (b,c) doubles as a buffer for column-c tiles.
- Corridor cells: 2k^2 n in total (k^2 rows and k^2 columns of length n), i.e. 2n per
  square out of s^2 = k n. Room needs s >= C k; here s = k^2.
- Crossings: row R(b,c) crosses k^2 columns; column C(c,a) crosses k^2 rows. A crossing cell
  belongs to neither corridor; slides step around it with an O(1) detour that restores it.

## One hop

hop1 (source S=(b,J) -> hub h=(b,c)), blank starting in h's reservoir:
  entry into R(b,c) O(s); slide along R(b,c) to block J: every slide moves a row tile one
  cell toward block c, efficient except O(1) per crossing, O(k^2); exit of T from S's
  reservoir into the row by the restoring three-row carry, 4d + O(k^2) with d <= s; the head
  drops into h's reservoir, O(s). Total O(s + k^2). Blank ends on T's old cell in S.
hop2 (hub h=(b,c) -> D=(a,c)), blank in D's reservoir:
  entry into C(c,a) O(s); vertical slide to band b: column tiles move toward band a,
  efficient except crossings O(k^2); exit of the class-D stock tile from h's reservoir into
  the column, O(s + k^2). Blank ends in h's reservoir.
Invariants: R(b,c) keeps target column c (T has it); C(c,a) stays pure (the stock tile is
class (a,c)). Reservoirs change only by the count update.

Every tile makes at most two hops, so hops cost O(n^2 (s + k^2)) = O(n^3/k + k^2 n^2).

## Rounds and relocations

T[S,D] = misplaced reservoir tiles at S of class D. After padding (home tiles as loops,
see "Irregularity"), T is Delta-regular with Delta <= s^2, so it splits into Delta perfect
matchings pi_r (Koenig). Rounds may be run in any order.

Round r: Euler circuit(s) of G_r on the k columns (edge S: col pi(S) -> col S). A closed trail
ends with the blank on its start square D0 (D0 was served first and sent last). Moving to the
next trail's start D0' is a *relocation*: a blank/tile swap (`two_inefficientMoves_le_of_blank_swap`),
cost O(n), which moves one tile t from D0' to D0 and nothing else. Choose t among D0''s
misplaced tiles: one count perturbation (T[D0',x] -1, T[D0,x] +1).
  relocations <= sum_r cycles_r <= C k Delta   (Lemma 2)  => cost O(k s^2 n) = O(n^3/k).

Carries (Lemma 1 failures): a vertical blank swap in column block c from a hub with stock to
the hub the schedule uses, O(n) each, one perturbation each. Need O(n^2/k) of them.

## Irregularity and perturbations

Row sums of T (tiles to send) and column sums (tiles to receive) differ where corridors,
seeds and the row prefill took tiles: sum of |deficiencies| = O(k^2 n + k^3 m). Each
relocation or carry adds one unit. Decompose the current T online, one matching per round,
covering every vertex of maximum degree (always possible in a bipartite multigraph). An
unmatched vertex makes G_r unbalanced by one, which costs at most half an extra trail, i.e.
half a relocation, which makes one more perturbation: the total is at most
  base * (1 + 1/2 + 1/4 + ...) = 2 * base,
with base = O(k^2 n + k^3 m) + (Lemma 2 relocations) + (Lemma 1 carries). Every perturbed tile
needs at most two extra hops: O(base * (s + k^2)), lower order. (To be written carefully:
the "half an extra trail" step and that padding keeps the decomposition within Delta rounds.)

## Setup and cleanup (all O(k^2 n^2))

- Columns C(c,a) filled with class (a,c): k^2 n tiles, O(n) each.
- Rows R(b,c) filled with their steady-state class pattern: k^2 n tiles at prescribed cells,
  O(n) each. Same kind of task as Zhong's Preparation for k^3 n corridor tiles at cost k^3 n^2;
  here the exact cell matters, which the staging (prefix solver toward any assignment) allows.
- Seeds: m tiles per class per hub, k^3 m tiles, O(n) each: O(k^3 m n) <= O(k^2 n^2) iff m <= s.
- Cleanup: row and column contents, stock and seeds, O(k^2 n + k^3 m) tiles moved home by
  blank swaps, O(n) each.
- Finish: each square solved locally, O(s^3) per square, k^2 s^3 = n^3/k.

## Total

  O(n^3/k + k^2 n^2 + n * (relocations + carries))
    = O(n^(8/3))  at k = n^(1/3), provided
  Lemma 1 (stock): carries = O(n^2/k), e.g. none with m = O(1) or O(s) seeds.
  Lemma 2 (trails): cycles per round = O(k) after merging, i.e. relocations O(k s^2).
  Lemma 3 (in flight): per column c and class x, the number of class-x tiles in the rows of
  column c stays within the column's seed slack of its initial (steady-state) value. Since
  inserts and demands of x match every round, column-level stock = seeds + in_flight(0) -
  in_flight(r) exactly, so Lemma 3 is necessary for Lemma 1.

Nothing else in the scheme has an unproved cost. The crossing detours (O(1) each) and the
row/column steady-state staging are the two geometric steps that need a closer look before
any formalization.

## Levers not yet used
- The order of the Delta rounds is free, and so is the choice of each matching: both can be
  used to keep in-flight counts stable (Lemma 3).
- Relocations are only needed per round when G_r is disconnected or the transition system
  splits; G_r was connected in every simulated round.

## Simulation status (eulerrun.py, after the own-hub correction)
m = 16, k = 8..12: no carries, no hard stalls, all stocks in [2, 37], ~1-2 trails per round.
Needed seeds grow slowly (worst dip ~8/13/14 at k = 8/10/12 on random). Own-hub service is
not free: it spends the own class's virtual stock (see NOTES.md, correction).
