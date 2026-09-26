# Beating n^(11/4): two-hop transport through hub squares (work in progress)

Status: theory sketch plus count-model simulations. Nothing is proved and nothing is formalized.

## Idea
Replace Zhong's k^3 n exact-class corridors with k^2 n corridors that only need to be
consistent in one coordinate:
- row R(b,c) in band b holds tiles whose target column block is c (any target band);
- column C(c,a) in column block c holds tiles of group (a,c) exactly.
A tile goes (b,J) -> hub (b,c) -> (a,c). The corner problem is handled by making the hub's
reservoir a random-access buffer: the row drops its head into the hub, and the hop2 carries
a class-(a,c) tile out of the hub (cost O(s)). Each hop is monotone, and each costs
O(s + k^2) inefficient moves (the k^2 is for crossing corridors).
Cost: 2n^2 hops * O(s) + corridor setup and arrangement O(k^2 n^2) + seeds + relocations.
With k = n^(1/3) this gives O(n^(8/3)), PROVIDED the number of stalls (relocations, O(n) each)
is O(n^2/k).

## Why hubs don't overflow
Hubs hold tiles only in transit, and the hop multigraph is balanced (in = out at every square).
In a "pooled" model (row + hub stock random access) with 1 seed per class per hub and a
replenish rule, the run never stalls (argument in session; easy).

## The open lemma (the crux)
Rows are delay lines. The tile a row delivers is its head, not the tile just inserted, and
insertions land at the source's distance (so the row is not FIFO). Hub stock of class a
= pool_a - (class-a tiles in flight in the row). Stalls come from transients: a burst of
class-a demand before the row's composition has adjusted.
Findings (scripts here, `uv run --with numpy python <script> kinds KxS,... m,...`):
- hubrun*.py: greedy policies stall a lot on transpose and rot90.
- randrun.py: randomized Algorithm 4 with pairing (insert the class just withdrawn). With
  seeds m = 2s, relocs*k/n^2 stays roughly 0.2-0.8 up to k = 12 (s = k^2): consistent with
  O(n^(8/3)), but blockperm creeps up. Pairing forces 2-cycles (transpose) = bursts.
- copyrun.py: insert the class just delivered. Fails, because near classes recirculate faster.
- rotorrun.py: round-robin insertion class per hub (breaks forced cycles). Fails on transpose
  because rows start uniformly mixed, while the steady state holds far classes more
  (in flight ~ s*ln k per class).
  (Steady-state rows: done in rotorrun2.py, see below.)
- Proof direction: rotor-router (Propp machine) discrepancy bounds for the hub walk, plus
  steady-state rows. Would give seeds O(s log k): O(n^(8/3) log n), still below 11/4.

## 2026-09-26 (cont.): steady rows, synchronization, Euler rounds

- rotorrun2.py: rows pre-filled with their steady state under rotor insertion (pre-simulated).
  Fixes transpose (relocs*k/n2 2.98 -> 0.0005 at k=6) and mostly rot90 (2.05 -> 0.024);
  blockperm unchanged and growing with k (0.27 at k=6, 1.0 at k=8), not helped by seeds up to 4s.
- Diagnosis (blockperm): row R(b,c) also carries the hub's own class (b,c), which lands home,
  not in stock. Transit stock at hub (b,c) is refilled at the rate the blank visits (b,c) as
  a *demand* square, which depends on the global walk. Visit rates of squares drift apart over
  long phases (hub (1,1): no such visit for the first 2600 steps), so stock drains by Theta(phase).
  **Stocks are fine iff every square is visited at the same rate** (up to the seed slack).
- syncrun.py: visit synchronization. Next source = least-visited allowed one; a source may lead
  the least-visited active square by < `lead` visits; else a sync relocation (O(n) carry).
  Stock stalls vanish once m >= 2*lead. With `look` (pick the hub whose band offers the
  least-visited source), all relocs*k/n2 at m=64, lead=32:
      random k=8: 0.067, k=10: 0.042;  blockperm k=10: 0.42 (~ number of sigma-cycles per round,
      ~ln k^2: fine);  transpose/rot90 k=10: ~0.01-0.03.
  Budget is relocs = O(n^2/k), i.e. <= O(k) per round of s^2 rounds; seeds up to m ~ s are
  affordable (k^3 m n <= k^2 n^2).
- eulerrun.py: the proof-shaped version. T[S,D] is s^2-regular (home tiles = loops), so it
  splits into s^2 perfect matchings pi_r (Koenig). In round r each square sends one tile (to
  pi_r(S)) and receives one. Square S is an edge col(pi S) -> col(S) of a multigraph G_r on
  the k columns with in = out = k everywhere; a round is an Euler circuit of G_r, so
      relocations per round <= #components(G_r) <= k, total <= k s^2 = n^2/k.   (the budget)
  At vertex c the walk pairs arrivals D (column-c squares) with departures S (col pi S = c);
  hub = (band S, c). Departures in the same band are interchangeable: free trail merging.
  Row inputs are fixed by pi_r, so row outputs are EXOGENOUS; per round each column-c class is
  inserted exactly once and demanded exactly once, and hub (b,c) serves exactly as many
  demands as it outputs (its total stock is invariant). What remains is an assignment problem:
  classes -> hubs with stock >= 1, capacities n_{b,c}. Cross-band swaps (to merge trails
  further) also change the assignment.

Results (eulerrun.py, `uv run --with numpy --with scipy python eulerrun.py kinds KxS m`).
Assignment per column = lexicographic max-weight matching (feasible pairs, then own-hub
pairs, then stock). Greedy and non-lexicographic weightings each broke one family
(greedy: blockperm k=12 carried one class every round; stock-first: random).
  m=16: hard stalls 0, carries 0 everywhere except transpose k=10 (2), k = 8..12.
  random: min stock stays >= 12-13 of 16 (stock barely moves); cycles/round 5.0/5.9/6.8
  (k=8/10/12, about 0.6k, within the k per round budget); transpose/rot90/blockperm 1-2.
  G_r always connected. (cycles+carry)*k/n2 <= 0.63 and not growing.
  So Euler rounds + MaxWeight assignment look like a working O(n^(8/3)) schedule with m = O(1).

## Open lemma, sharpened
Column c, hubs b, classes a. Supply O^r_b (row outputs, exogenous; column sums fluctuate with
in-flight counts), per round a b-matching classes -> hubs with capacities n^r_b = |O^r_b|.
Want: a policy (MaxWeight = serve from the fullest hub) keeping stock_b[a] >= 1 with seeds
m = O(s) (or polylog), while also allowing enough cross-band swaps that cycles per round
stay O(k) (no proof yet that merging leaves <= O(k) cycles; data: about 0.6k on random).
This looks like a fully loaded input-queued switch with deterministic admissible
arrivals; MaxWeight/rounding discrepancy results (Tassiulas-Ephremides; Tijdeman's chairman
assignment) are the tools to try. Also needed: in-flight fluctuation of class a in column c
is O(seeds) (rows in steady state; latency <= row length in hops).
