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
      random k=8: 0.067, k=10: 0.042, k=12: 0.016 (m=96, lead=48);  blockperm k=10: 0.42 (~ number of sigma-cycles per round,
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
Assignment per column = lexicographic max-weight matching (feasible pairs, then stock).
CORRECTION: earlier runs (commits 8e2bef6, fcad46d) treated service of D=(a,c) by its own
hub as free. It is not: D then receives R(a,c)'s head, whatever class it is, so the own class
needs (virtual) stock like any other. With that free, own-class deficits reached -s^2
(blockperm) and surplus stock ~s^2 piled up elsewhere: cleanup ~n^3. Those "0 carries" were
an artifact. With the own class treated like the others (virtual seeds m):
  m=16, k=8..12, all four families: carries 0, hard 0; every stock in [2, 37].
  Worst dip below the seed level on random: ~8/13/14 at k=8/10/12 (m=2,4 fail with hard
  stalls: column-level stock of a class runs out, i.e. in-flight fluctuation, Lemma 3).
  cycles/round: 1.0-2.0 on all families (random ~1.46); G_r always connected.
  So seeds m = O(1)-ish (slowly growing, far below the affordable m ~ s) seem to suffice.

## Open lemma, sharpened
Column c, hubs b, classes a. Supply O^r_b (row outputs, exogenous; column sums fluctuate with
in-flight counts), per round a b-matching classes -> hubs with capacities n^r_b = |O^r_b|.
Want: a policy (MaxWeight = serve from the fullest hub) keeping stock_b[a] >= 1 with seeds
m = O(s) (or polylog), while also allowing enough cross-band swaps that cycles per round
stay O(k) (no proof yet that merging leaves <= O(k) cycles; data: ~1.5 per round).
This looks like a fully loaded input-queued switch with deterministic admissible
arrivals; MaxWeight/rounding discrepancy results (Tassiulas-Ephremides; Tijdeman's chairman
assignment) are the tools to try. Also needed: in-flight fluctuation of class a in column c
is O(seeds) (rows in steady state; latency <= row length in hops).

## Proof plan for the three lemmas (2026-09-26, pen and paper; see ACCOUNTING.md)

Lemma 2 (trails) can be made unconditional. A round may split into up to k^2 closed trails,
but start them in snake order over the k x k squares: the relocations of one round then
cost O(k^2 s) = O(k n) in total, i.e. O(k n s^2) = O(n^3/k) over all rounds. Each relocation
is a blank/tile swap moving one misplaced tile t_{i+1} of the next start square Z_{i+1} into
the previous start Z_i. Along the chain every start square gives one misplaced tile and gets
one, so T keeps its row and column sums (only entries move) and the online decomposition
(one perfect matching of the current regular T per round) continues. The moved tiles need
no extra hops beyond their own transport. Needs care: Z_{i+1} must have a misplaced tile
other than its round tile (else use the round tile and re-plan that square's round).

Lemma 1 (stock) reduces to an online rounding problem, per column c:
  given fractional b-matchings y_t on hubs x classes (row sums n_b(t), column sums 1) with
  sum_{r<=t} (O_r - y_r) bounded (O_r = row outputs; possible iff Lemma 3), choose integral
  b-matchings P_t online with |sum_{r<=t} (y_r - P_r)[b,a]| <= f(k) for all t.
  Seeds m = f(k) + O(1) suffice, and m up to s = k^2 is affordable, so f(k) = O(k^2) is enough.
- Offline (all y_t known): Barany-Grinberg style floating rounding keeps at most d = k^2
  rounds fractional, so f <= k^2. But y_t is not fully known in advance: relocations move
  tiles and the decomposition is online.
- Online: MaxWeight (P_t = argmax_P <D, P>, D = cumulative deficit) gives
  Delta(|D|^2) <= 2<D, y_t - P_t> + 2k <= 2k: only O(sqrt(k t)). Bounded f needs negative drift,
  which holds when y_t stays inside its face: if y_t[b,a] >= delta on the support, then
  max_P <D,P> >= <D,y_t> + delta*|D| (D has zero row and column sums), so |D| = O(k/delta).
  Choose y_t as smoothed long-run rates (any y with bounded cumulative gap to O works), not
  the raw sparse O_t. Open: delta for adversarial boards; supports that change over time.
- Literature: Ajtai, Aspnes, Naor, Rabani, Schulman, Waarts, "Fairness in scheduling",
  J. Algorithms 29 (1998): online carpool/edge orientation, deterministic greedy unfairness
  <= n/2 (tight); "vector rounding" (sum-preserving only) reduces to it. Our rounding must
  preserve row AND column sums (b-matchings), which is not covered as such. Tijdeman's
  chairman assignment (one class at a time, discrepancy < 1) handles each class alone but
  not the hub capacities n_b(t).

Lemma 3 (in flight) is the remaining genuinely new question: column-level stock of class x
equals seeds + in_flight_x(0) - in_flight_x(t) exactly. Levers: order of rounds (free),
choice of each matching, steady-state prefill. Data: dips ~14 at k = 12 on random.
