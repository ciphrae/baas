# An O(n^(8/3) (log n)^(1/3)) bound on inefficient moves (proof, pen and paper)

Claim. Every reachable n x n board has a solution with O(n^(8/3) (log n)^(1/3)) inefficient
moves (k = (n/log n)^(1/3)); with k = n^(1/3) the same proof gives O(n^(8/3) log n). Both
beat Zhong's n^(11/4). Simulations suggest the log factor is an artifact of Lemma 4.

Status: complete argument at the level of a paper sketch. Everything specific to this scheme
is proved below. The primitive moves (entry and exit of a reservoir, corridor slides,
parity-adjusted jumps over corridor rows, blank/tile swaps, local Finish, staging) are the ones
already formalized for Zhong's scheme and are used with their existing costs. Section 8
lists what still needs checking; none of it is a known gap.

## 1. Layout

n = k s, k x k squares of side s, square (a,c) = band a, column block c. Assume
s >= C k log n (true for k ~ n^(1/3)).

- Rows R(b,c) (k per band, one per target column block c): the top k board rows of band b.
  R(b,c) holds tiles whose target column block is c, any band. Two halves, left and right
  of block c; the head of each half is at the edge of block c, next to hub (b,c).
- Columns C(c,a) (k per column block, one per target band a): board columns inside block c,
  below each band's row group. C(c,a) holds exactly class (a,c). Two halves, above and below
  band a. Where a column meets a band's row group it is interrupted; vertical travel crosses
  the k rows by a parity-adjusted jump, O(k) (as `Transport/Jumps.lean`).
- Reservoir of square (b,c): the rest of the square. It doubles as hub (b,c): tiles of class
  (x,c), x != b, stored there are its *stock*.
Corridor cells: 2 k^2 n.

## 2. Phases

1. Preparation, O(k^2 n^2 log n). All choices below follow fixed rules that do not look at
   the transport dynamics.
   - fill every C(c,a) with class (a,c) tiles;
   - fill every row half with arbitrary tiles of its target column block (*prefill*);
   - give every square a *reserve* of R = 8n(1 + ln(k s^2)) + C k^2 log n home tiles
     (bring own-class tiles in if it has fewer), plus one for relocations.
   O(k^2 n log n) tiles, each moved O(n) by the staging machinery (as in Zhong's Preparation).
   No stock is seeded: hubs start empty.
2. Transport (sections 3-6).
3. Cleanup: every tile not in its target square after Transport (row and column contents,
   leftover stock, floating tiles), O(k^2 n log n) of them, goes home by blank swaps,
   O(n) each: O(k^2 n^2 log n).
4. Finish: solve each square locally: k^2 * O(s^3) = O(n^3/k).

## 3. The transport plan

After Preparation, let T[S,D] be the number of tiles in the reservoir of S whose target
square is D != S. A square's sends and receives differ by its class tiles held in corridors
and by Preparation's bookkeeping: total imbalance I = O(k^2 n log n). Add I *dummy* edges
(from squares with surplus receives to squares with surplus sends) and loops (home tiles)
to get a Delta-regular bipartite multigraph, Delta <= s^2. By Koenig it is a union of Delta
perfect matchings pi_r. **Run the rounds in a uniformly random order**; section 6 shows that
some order has the needed property.

## 4. One round

Walk the cycles of pi_r backwards. For a cycle D_0, D_1 = pi^-1(D_0), D_2 = pi^-1(D_1), ...,
the blank starts in D_0's reservoir.
  (serve D_j) with S = D_{j+1}, a = band D_j, c = col D_j, b = band S, J = col S:
  - J = c (same column): S's round tile is class D_j and already in block c: hop2 from S
    straight along C(c,a). No stock involved.
  - b = a (same band): hop1 from S into D_j itself along R(a,c): S's tile enters the row at
    block J, D_j receives the row's head. (Own hub: no stock needed.)
  - otherwise, if hub (b,c) has a class-D_j stock tile: hop2 moves it along C(c,a) into D_j;
    the blank is now in hub (b,c). Then hop1 into hub (b,c): S's round tile (class D_j)
    enters R(b,c) at block J, the row's head drops into the hub (stock, or home if it is
    class (b,c)).
  - otherwise (*bypass*): a blank/tile swap moves the blank from D_j to hub (b,c) and one of
    the hub's reserve home tiles into D_j (O(n), inside column block c). Then the same hop1.
    D_j's class tile is owed until Cleanup; the tile it got is a column-c tile, i.e. stock
    of hub D_j (extra stock never hurts).
  The blank ends in S's reservoir: S sent its round tile. Next j.
The cycle closes when the blank is back at D_0 (D_0 served first, sent last).
Dummy edges cut cycles into paths (section 5).
**The insertions, hence all row dynamics, are exactly those of the plan, bypass or not.**

Hop costs (as Zhong's transfer pieces): entry O(s); corridor slides efficient except O(k)
per crossed row group, O(k^2); exit of a chosen reservoir tile into a corridor (restoring
three-row carry) O(s + k^2); the row head drop O(s). hop1 inserts at the far edge of the
source block: position p_d = (d+1) s - 1 for block distance d (moving the tile inside its
own square, O(s)).
Every tile makes at most two hops: O(n^2 (s + k^2)) = O(n^3/k + k^2 n^2).

**Lemma 1 (stock identity).** For hub (b,c) and class x != b (of column c), at all times
    stock_b[x] = out_b[x] - new_b[x] + bypass_b[x],
where out_b[x] = prefill tiles of class x that have left R(b,c), new_b[x] = class-x tiles
inserted during Transport and still in R(b,c), and bypass_b[x] = bypasses so far.
*Proof.* Stock gains every class-x head dropping into the hub and loses every service from
stock. Every demand for x at hub (b,c) (served or bypassed) is followed by one insertion of
a class-x tile into R(b,c), and nothing else inserts there. Heads of new tiles = inserted -
new_b[x] = demands - new_b[x]; services = demands - bypasses. []

**Corollary.** A bypass happens only when stock_b[x] = 0, and then leaves it at 0 (the
insertion follows). At the last bypass t*, bypass_b[x] = new_b[x](t*) - out_b[x](t*), so
    bypass_b[x] <= N_b[x] := max_t new_b[x](t).
So each hub makes at most sum_x N_b[x] bypasses, and needs that many reserve tiles.

## 5. Relocations and floating tiles

A relocation moves the blank from square E to square Z by a blank/tile swap
(`two_inefficientMoves_le_of_blank_swap`), O(dist) moves, moving exactly one tile, from Z
to E; nothing else changes.
- Cycles. After a cycle closes at D_0, relocate to the start of the next cycle. Choose each
  cycle's start as its first square in a fixed snake order of the k x k squares and run the
  cycles in that order: the relocations of one round cost O(k^2 s) in total, whatever their
  number. Over Delta <= s^2 rounds: O(k^2 s^3) = O(n^3/k). Each square holds at most one
  *floating* tile (a misplaced tile outside the plan). The start Z gives its floating tile
  to E; for a cycle the start is also the end, so it gets one back when the cycle closes.
  If a start has none, it gives a reserve home tile (one per square is set aside); that
  creates one new floating tile.
- Paths (dummy edges). A path ends at a square that sent without being served (hole) and the
  next one starts at a square served without sending. One relocation of cost O(n) per dummy
  edge, and at most one new floating tile: O(I n) = O(k^2 n^2 log n).
- Round boundaries: O(n) each, O(s^2 n).
Floating tiles are never touched by the plan; there are O(I + k^2) of them; Cleanup.

## 6. In-flight bound (the only probabilistic step)

Fix a row half H of R(b,c), length L <= n. Its insertions come from block distances d with
positions p_d = (d+1)s - 1. Let g_d(r) = number of insertions at distance d in round r,
beta_{>=d} = (1/Delta) sum_r sum_{d' >= d} g_d'(r) (average rate), and for class x,
alpha_{x,d} = (1/Delta) * (number of rounds whose x-insertion into H is at distance d).

**Lemma 2 (push).** A tile at position <= p leaves H after at most p+1 insertions into H at
positions >= p. *Proof.* An insertion at position q' shifts cells 1..q' one step toward the
head and outputs cell 0; a tile at position q <= p <= q' moves to q-1. []

**Lemma 3 (windows).** Let w_d = min(Delta, ceil(2(p_d+1)/beta_{>=d})). With probability
1 - n^{-5} over the random order, for all H, d, x and every window of w_d consecutive rounds:
(a) if w_d < Delta, the window has >= p_d + 1 insertions into H at distance >= d;
(b) the window has at most 2 alpha_{x,d} w_d + C log n rounds inserting x into H at distance d.
*Proof.* A window of a uniformly random order is a uniformly random w-subset of the Delta
matchings, so both counts are sums sampled without replacement, to which Bernstein's
inequality applies (Hoeffding's comparison with sampling with replacement).
(a) mean mu = w_d beta_{>=d} >= 2(p_d+1), terms in [0,k], variance <= k mu:
P(sum <= mu/2) <= exp(-mu/(10k)) <= exp(-s/(5k)) <= n^{-20} since s >= C k log n.
(b) terms in {0,1}, mean alpha w_d: P(sum >= 2 alpha w_d + C log n) <= n^{-20}.
Union bound over Delta windows, 2k^2 halves, k distances, k classes: poly(n) events. []

**Lemma 4 (in flight).** On the event of Lemma 3,
    N_b[x] <= sum over the two halves H and distances d of (2 alpha_{x,d} w_d + C log n),
and for every hub, sum_x of the right side is <= 8 n (1 + ln(k Delta)) + O(k^2 log n).
This bound does not depend on T.
*Proof.* If w_d < Delta, by Lemma 3(a) and Lemma 2 a tile inserted at distance d leaves H
within w_d rounds, so the x's in H from distance d at any time were inserted in the last w_d
rounds: at most 2 alpha w_d + C log n by (b). If w_d = Delta the count is at most
alpha Delta = alpha w_d. For the sum, with gamma_d = sum_x alpha_{x,d} (all insertions at
distance d), sum_x sum_d 2 alpha_{x,d} w_d <= sum_d 4 (p_d+1) gamma_d / beta_{>=d}
<= 4 L sum_d gamma_d/(gamma_d + gamma_{d+1} + ...) <= 4 L (1 + ln(beta_{>=0}/gamma_last))
<= 4 L (1 + ln(k Delta)), since nonzero rates are >= 1/Delta and beta <= k. Two halves,
L <= n. []

So the reserve R of section 2 covers every bypass: no hop ever fails, and the bypasses cost
O(n) each, O(k^2 n log n) of them: O(k^2 n^2 log n). Since the bound holds for every T,
the reserve is fixed before T is known.

## 7. Total

    O(n^3/k)              hops, cycle relocations, Finish
  + O(k^2 n^2)            corridor crossings, corridor filling
  + O(k^2 n^2 log n)      reserves, bypasses, dummy-edge relocations, Cleanup
With k = (n / log n)^(1/3): O(n^(8/3) (log n)^(1/3)).

## 8. To check before formalizing

1. Geometry of the layout: k row corridors per band plus hubs, column corridors crossing
   row groups by jumps, room for everything with s ~ k^2 (Zhong needed s >= k^3 only for the
   staging of k^3 n corridor tiles; here there are O(k^2 n log n)).
2. Preparation filling rows, columns and reserves in O(k^2 n^2 log n): same staging idea as
   Zhong's (stage in a prefix, spread by row/column schedules), with O(k^2 n log n) tiles.
3. Reserves: a square with too few home tiles gets them from its sources; this only changes T
   (by fixed rules) before the plan is made.
4. Parity: every hop is a count update (as in Zhong's formalization, `GroupEquivalent`).
5. For Lean: the proof only needs *some* order satisfying Lemma 3, i.e. a counting argument
   over permutations of the Delta matchings (probabilistic method), or an explicit order.
6. Cleanup of O(k^2 n log n) misplaced tiles by blank swaps O(n) each (square-level
   permutation, cycle by cycle), and the owed class tiles of bypassed squares among them.

Simulations (pairrun.py, random order, naive uniform prefill, seeds instead of bypasses):
seeds needed per hub <= 0.85 n and in total <= 0.23 k^2 n for random, transpose, rot90,
blockperm at k = 4..12, not growing.
