# An O(n^(8/3) log n) bound on inefficient moves (proof, pen and paper)

Claim. Every reachable n x n board has a solution with O(n^(8/3) (log n)^(1/3)) inefficient
moves (with k = (n/log n)^(1/3)); with k = n^(1/3) the same proof gives O(n^(8/3) log n).
Both beat Zhong's n^(11/4). Simulations suggest the log factor is an artifact of Lemma 4.

Status: complete argument at the level of a paper sketch, except the seed circularity
(section 8, item 3), which is open. Everything specific to this scheme
is proved below. The primitive moves (entry and exit of a reservoir, corridor slides,
parity-adjusted jumps over corridor rows, blank/tile swaps, local Finish) are the ones already
formalized for Zhong's scheme and are used with their existing costs. Items to double-check
are listed at the end.

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
Corridor cells: k^2 n + k^2 n.

## 2. Phases

1. Preparation, O(k^2 n^2 log n):
   - fill every C(c,a) with class (a,c) tiles;
   - fill every row half with arbitrary tiles of its target column block (*prefill*);
   - put seeds_b[x] tiles of class (x,c) into hub (b,c)  (Lemma 4: sum over x <= O(n log n));
   - make sure every square holds at least one home tile.
   O(k^2 n log n) tiles, each moved O(n) by the staging machinery (as in Zhong's Preparation).
2. Transport (sections 3-6).
3. Cleanup: every tile not in its target square after Transport (row and column contents,
   leftover stock, floating tiles), O(k^2 n log n) of them, goes home by blank swaps,
   O(n) each: O(k^2 n^2 log n).
4. Finish: solve each square locally: k^2 * O(s^3) = O(n^3/k).

## 3. The transport plan

After Preparation, let T[S,D] be the number of tiles in the reservoir of S whose target
square is D != S. Row sums (sends) and column sums (receives) of a square differ by the
number of its class tiles held in corridors and stock (plus prefill/seed bookkeeping):
the total imbalance is I = O(k^2 n log n). Add I *dummy* edges (from squares with surplus
receives to squares with surplus sends) and loops (home tiles) to get a Delta-regular
bipartite multigraph, Delta <= s^2. By Koenig it is a union of Delta perfect matchings pi_r.
**Run the rounds in a uniformly random order.** (Section 6 shows a good order exists.)

## 4. One round

Walk the cycles of pi_r backwards. For a cycle D_0, D_1 = pi^-1(D_0), D_2 = pi^-1(D_1), ...:
the blank is in D_0's reservoir.
  (serve D_j) with S = D_{j+1}, a = band D_j, c = col D_j, b = band S, J = col S:
  - J = c (same column): S's round tile is class D_j and already in block c: hop2 from S
    straight down C(c,a). No stock involved.
  - b = a (same band): hop1 from S into D_j itself along R(a,c): S's tile enters the row at
    block J, D_j receives the row's head. (Own class: no stock needed.)
  - otherwise: hop2: a class-D_j stock tile of hub (b,c) goes down/up C(c,a) into D_j; then
    hop1 into hub (b,c): S's round tile (class D_j) enters R(b,c) at block J, the row's head
    drops into the hub (it becomes stock, or is home if it is class (b,c)).
  The blank ends in S's reservoir: S sent its round tile. Next j.
The cycle closes when the blank is back at D_0 (D_0 served first, sent last).
Dummy edges cut cycles into paths (section 5).

Hop costs (as Zhong's transfer pieces): entry O(s); corridor slides efficient except O(k)
per crossed row group, O(k^2); exit of a chosen reservoir tile into a corridor (restoring
three-row carry) O(s + k^2); the row head drop O(s). hop1 inserts at the far edge of the
source block: position p_d = (d+1) s - 1 for block distance d (moving the tile inside its
own square, O(s)).
Every tile makes at most two hops: O(n^2 (s + k^2)) = O(n^3/k + k^2 n^2).

**Lemma 1 (stock identity).** For hub (b,c) and class x = (x,c), x != b, at all times
    stock_b[x] = seeds_b[x] + prefill_b[x] - inflight_b[x],
where inflight_b[x] = number of class-x tiles in the two halves of R(b,c).
*Proof.* Stock changes by +1 for each class-x head that drops into hub (b,c) and by -1 for
each service of x from hub (b,c). By the pairing, every such service is immediately followed
by the insertion of a class-x tile into R(b,c), and nothing else inserts into R(b,c). Rows
have fixed length, so inserted x's = x's output + change in inflight. Summing:
stock - seeds = outputs - services = outputs - inserts = prefill - inflight. []

So the hop2 never fails iff inflight_b[x] <= seeds_b[x] + prefill_b[x] - 1 before each
service. Enough: seeds_b[x] >= 1 + max_t (number of class-x tiles inserted during Transport
and still in R(b,c) at t) =: 1 + N_b[x].

## 5. Relocations and floating tiles

A relocation moves the blank from square E to square Z by a blank/tile swap
(`two_inefficientMoves_le_of_blank_swap`), O(dist) moves, moving exactly one tile, from Z
to E; nothing else changes.
- Cycles. After a cycle closes at D_0, relocate to the start of the next cycle. Choose each
  cycle's start as its first square in a fixed snake order of the k x k squares and run the
  cycles in that order: the relocations of one round cost O(k^2 s) in total, whatever their
  number. Over Delta <= s^2 rounds: O(k^2 s^3) = O(n^3/k). Each square keeps one *floating*
  tile (a misplaced tile outside the plan; initially one per square, from one removed
  matching). The start Z gives its floating tile to E; for a cycle, the start is also the
  end, so it gets one back when the cycle closes. If a start has none, it gives a home tile
  instead; that creates one new floating tile (at E).
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

**Lemma 3 (windows).** With w_d = ceil(2(p_d+1)/beta_{>=d}) (capped at Delta), with
probability 1 - O(k^7 e^{-ck}) over the random order: every window of w_d consecutive
rounds has >= p_d + 1 insertions into H at distance >= d, for all H, d; and every window of
w_d rounds contains at most 2 alpha_{x,d} w_d + C k rounds inserting x into H at distance d,
for all H, d, x.
*Proof.* A window of a uniformly random order is a uniformly random w-subset of the Delta
matchings, so both counts are sums sampled without replacement. The first has mean
w_d beta_{>=d} >= 2(p_d+1) and terms in [0,k] with variance <= k beta; Bernstein (valid
without replacement, Hoeffding's reduction) gives failure probability
exp(-Omega(p_d/k)) <= exp(-Omega(s/k)). The second has terms in {0,1} and mean
alpha w_d; Bernstein gives <= 2 alpha w_d + C k except with probability e^{-Omega(k)}.
Union bound over <= Delta windows, 2k^2 halves, k distances, k classes. []

**Lemma 4 (seeds).** On the event of Lemma 3,
    N_b[x] <= sum over the two halves and d of (2 alpha_{x,d} w_d + C k),
and for every hub sum_x of the right side is <= 8 n (1 + ln(k Delta)) + O(k^3) = O(n log n).
*Proof.* By Lemmas 2-3 a tile inserted at distance d is out within w_d rounds, so the x's
in H at time t were inserted in the last w_d rounds, per distance. For the sum: with
gamma_d = sum_x alpha_{x,d} (<= total insertion rate at distance d),
sum_x sum_d 2 alpha_{x,d} w_d <= sum_d 2 gamma_d (2(p_d+1)/beta_{>=d} + 1)
  <= 4 L sum_d gamma_d / beta_{>=d} + 2k,  and  sum_d gamma_d/(gamma_d + gamma_{d+1} + ...)
  <= 1 + ln(beta_{>=0} / gamma_last) <= 1 + ln(k Delta)   (nonzero rates are >= 1/Delta). []

The bound depends only on the multiset of matchings, not on the order, so seeds can be fixed
in advance (up to the circularity that seeds are placed before T is known: compute them from
the pre-Preparation traffic with a factor-2 margin; the O(k^2 n log n) tiles moved by
Preparation change each rate by a negligible amount. To be written out.)

## 7. Total

    O(n^3/k)              hops, cycle relocations, Finish
  + O(k^2 n^2)            corridor crossings, corridor filling
  + O(k^2 n^2 log n)      seeds, dummy-edge relocations, Cleanup
With k = (n / log n)^(1/3): O(n^(8/3) (log n)^(1/3)).

## 8. To double-check before formalizing

1. Geometry of the layout: k row corridors per band plus hubs, column corridors crossing
   row groups by jumps, room for everything with s ~ k^2 (Zhong needed s >= k^3 only for the
   staging of k^3 n corridor tiles; here there are O(k^2 n log n)).
2. Preparation filling rows, columns and seeds in O(k^2 n^2 log n): same staging idea as
   Zhong's (stage in a prefix, spread by row/column schedules), with O(k^2 n log n) tiles.
3. **The seed circularity (open).** Seeds are computed from the rates alpha, beta of the
   plan, but taking seed and prefill tiles from their sources changes the plan. Split
   T = T_main + T_extra: T_main = original entries minus removed tiles (run in random rounds),
   T_extra = tiles displaced by Preparation plus dummies, O(k^2 n log n), delivered by direct
   O(n) carries at the end. Then alpha only decreases; beta can drop. If every route (H, >= d)
   keeps at least half of its traffic, w at most doubles and seeds from the original rates
   with a factor 4 suffice. So it is enough to take the removed tiles only from routes where
   they are at most half the traffic. Open: that a class whose seed need is a large fraction
   of its traffic can always be seeded this way (the bound gives need <= O(k n) per class
   against traffic ~ s^2 = k n per class at s = k^2: same order, so constants matter), or a
   different source of seeds. Also: a single hub's seed need must fit in its reservoir
   (O(n log n) << s^2: fine).
4. Lemma 3's constants: needs s/k >= C log n.
5. Parity: every hop is a count update (as in Zhong's formalization, `GroupEquivalent`).
6. The derandomization for Lean: the proof only needs *some* order satisfying Lemma 3;
   formally this is a counting argument over permutations (or an explicit order to be found).

Simulations (pairrun.py, random order, naive uniform prefill): seeds per hub <= 0.85 n and
total <= 0.23 k^2 n for random, transpose, rot90, blockperm at k = 4..12, not growing.
