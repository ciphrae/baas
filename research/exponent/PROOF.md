# An O(n^(8/3) (log n)^(1/3)) bound on inefficient moves

Pen-and-paper proof, now fully formalized in `SlidingPuzzle/Hub/` (theorems
`SlidingPuzzle.Hub.average_optimal_length`, `gods_number`); `LEAN_PLAN.md` records how the
Lean proof is organized and where it departs from this text (three-cycle insertions, straight
jumps for relocations and bypasses, no tokens, cleanup by double swaps, `k` even). Compared with
Zhong's n^(11/4) algorithm (Zhong 2023), the new parts are the layout (section 1), the
transport plan and its execution (sections 3-5), the in-flight bound (section 6) and a
Cleanup phase (section 7). The division into squares, the local Finish and the statistical
reduction follow the paper.

The formalization now certifies the explicit boardwise bound
`OPT(B) ≤ M(B) + 19319·n^(8/3)(ln n)^(1/3)` for `n ≥ 4096`.
The argument below retains its original asymptotic parameters; the current
numerical budgets and their derivation are in
[LEAN_PLAN.md](LEAN_PLAN.md#asymptotics) and
[PROOF_NOTES.md](../../PROOF_NOTES.md).

**Theorem.** Every reachable n x n board has a solution with
O(n^(8/3) (log n)^(1/3)) inefficient moves.

Parameters: k ~ (n/ln n)^(1/3), s = n/k, so s = Theta(n^(2/3) (ln n)^(1/3)). We need
  (P1) s >= 80 k ln n          (Lemma 3)
  (P2) 4k + 4 <= s             (room for corridors; insertion positions >= s/2)
and set R := 4n(1 + ln(k s^2)) + 64 k^2 ln n + 10k (reserve for bypasses, Lemma 4).
All hold for large n. Sides not of the form k*s are reduced to this case by solving the
outer n - k*s < k layers with a Parberry-style prefix (`Hub/AsympBound.lean`).

Cost units: "O(x)" below always counts inefficient moves (`Path.inefficientMoves`); via
`length + M(end) = M(start) + 2*ineff` this is what the final theorem needs.

## 0. Primitives

- **Blank/tile swap** (`exists_vertical_jump`, `exists_horizontal_jump`, and the L-shaped
  combination): the blank moves from cell u to cell v, the tile at v moves to u, every other
  tile ends where it was. Length O(dist(u,v)) if u, v have opposite colours. Otherwise first
  move the blank to a neighbour u' of u (this moves the tile at u' to u), then swap: we always
  take u' in the same reservoir as u, so the extra displacement is inside one reservoir.
  Inefficient moves <= (length + dist)/2 (`two_inefficientMoves_le_of_blank_swap`).
- **Corridor slide** (`Moves/Corridor.lean`): the blank walks along a line of cells, each
  step moving the next tile one cell back. A step is efficient iff it moves that tile toward
  its target.
- **Restoring exit**: a chosen reservoir tile T at distance d from the reservoir side is
  carried out next to a corridor cell by a three-row carry, and the reservoir is restored
  exactly; 4d + O(k^2) inefficient moves (entry column chosen so that d is odd). The Lean
  proof avoids it: insertions use three-cycles in local boxes (`LEAN_PLAN.md`, item 2).
- **Local Finish** (`Algorithm/Finish.lean`): when every square holds exactly its own
  tiles, solve each square locally; k^2 * O(s^3) = O(n^3/k).

## 1. Layout

Square (a,c): rows [a s, (a+1) s), columns [c s, (c+1) s). Offsets inside a square are
(row offset, column offset) in [0,s)^2.

- **Row corridors.** R(b,c) = board row b s + c, for c < k: the top k rows of every band are
  row corridors, one per target column block. R(b,c) consists of
    left half  = columns [0, c s),        position q <-> column c s - 1 - q,
    right half = columns [(c+1) s, n),    position q <-> column (c+1) s + q,
  and the *landing strip* = columns [c s, (c+1) s) of that row, which belongs to hub (b,c).
  Invariant (clean tile): a tile in a half whose target column block is c.
- **Column corridors.** C(c,a) = board column c s + a, for a < k, restricted to row offsets
  >= k (below each band's row group), in all bands except band a:
    upper half = bands < a, position q = distance (in cells of the corridor, skipping row
    groups) from band a; lower half = bands > a.
  In band a, column c s + a is ordinary reservoir of square (a,c). Clean tile: class (a,c).
- **Reservoir of square (b,c)** = row offsets [k, s) x column offsets [k, s), plus the landing
  strip of R(b,c). It doubles as **hub (b,c)**.
Corridor cells: at most k^2 n (rows) + k^2 n (columns). (P2) leaves a nonempty reservoir.

Compared with `Algorithm/Partition.lean`: `horizontal` keeps only its upper row (one row per
group, content relaxed to "target column block"), `vertical` shrinks from k^2 to k columns
per square and becomes indexed by target band, `Dims` drops `k^3 <= s` (no staging).

Travel costs:
- along a row half: no crossings (column corridors stop below the row groups);
- along a column half: each band it passes has a row group of k rows, crossed by a vertical
  blank/tile swap of length O(k): O(k^2) per hop;
- from a reservoir into its own row group or back: O(k), always by a blank/tile swap, which
  restores the other rows of the group it crosses (never by walking through them).

## 2. Phases

There is **no Preparation**. Corridors start with whatever tiles the board has there
(*junk* unless clean by chance).

1. Transport (sections 3-6) on the initial board.
2. Cleanup (section 7): O(k^2 n log n) misplaced tiles go home, O(n) each.
3. Finish: as formalized.

## 3. The plan

Let T[S,D] = number of reservoir tiles of S with target square D != S (the blank's cell is
ignored). sends(S) = sum_D T[S,D], recv(S) = sum_S' T[S',S]. The totals are equal, and
    recv(S) - sends(S) = (corridor cells in S's square) - (class-S tiles in corridors),
so |recv(S) - sends(S)| <= 2ks and the total surplus is I <= 2k^3 s = 2k^2 n.

**Dummy edges and padding.** Add I dummy edges Z -> E from squares with recv > sends to
squares with sends > recv (each square gets |recv - sends| <= 2ks of them), then loops
S -> S until every square has out-degree = in-degree = Delta_0 := max_S max(sends, recv)
<= s^2. This is a Delta_0-regular bipartite multigraph (sender copies x receiver copies);
by Hall/Koenig it is a disjoint union of Delta_0 perfect matchings (Lean: repeatedly extract
a perfect matching of a regular bipartite multigraph via Hall's theorem,
`Finset.all_card_le_biUnion_card_iff_exists_injective`).

**Reserves.** Set aside Q := R + 2ks + 2 + 2ks of these matchings (all of them if
Delta_0 <= Q). In a set-aside matching, a square's out-edge is a real tile (it stays in place
and becomes a *reserve* tile of that square), a loop (a home tile, also a reserve tile) or a
dummy (nothing). A square has at most 2ks dummy out-edges, so it gets >= R + 2ks + 2 reserve
tiles. Its set-aside in-edges are owed to it until Cleanup. Removing whole matchings keeps
every square balanced: no new dummy edges. The remaining Delta = Delta_0 - Q matchings are
the plan. (If Delta_0 <= Q everything goes to Cleanup: O(Q k^2 n) = O(k^2 n^2 log n).)

**Roles.** A reservoir tile is either *scheduled* (an out-edge of a plan matching not yet
executed) or has one of the roles *home* (its class is the square), *stock* (it dropped in as
a row head, class (x,c) of the hub's column with x != the hub's band), *reserve*, or
*floating* (anything else). Roles are bookkeeping only; they change only as stated below.

**Order.** Fix an order of the Delta plan matchings satisfying Lemma 3 (section 6); a
uniformly random order works with probability > 0.

## 4. One round

Round r executes pi = pi_sigma(r). Real edges S -> D: S sends one tile of class D (one of
its scheduled tiles with target D), D receives one.

**Walk.** A loop S -> S means S is idle this round. Consider the functional graph
D -> pi^-1(D) on squares with a real incoming edge.
Its components are cycles (no dummy edge) and paths (cut at dummy edges): a path starts at
a square Z whose out-edge is dummy (Z is served but sends nothing) and ends at a square E
whose in-edge is dummy (E sends but is not served). For each component, the blank starts in
the reservoir of its first square D_0 and repeats, for j = 0, 1, ...:

  **serve D_j** (skip if D_j's in-edge is dummy: the component ends here), with
  S = D_{j+1} = pi^-1(D_j), a = band(D_j), c = col(D_j), b = band(S), J = col(S):
  (i) J = c: S's scheduled tile of class D_j is in block c. hop2 from S: see below, with the
      stock tile replaced by S's tile. No stock involved.
  (ii) J != c, b = a: hop1 from S into D_j itself (hub (a,c)). D_j receives R(a,c)'s head.
  (iii) J != c, b != a, hub (b,c) has a class-D_j stock tile: hop2 from hub (b,c) into D_j,
      then hop1 from S into hub (b,c).
  (iv) J != c, b != a, no such stock tile: **bypass**: blank/tile swap from D_j's reservoir to
      a reserve tile of hub (b,c) (the blank goes to hub (b,c), the reserve tile to D_j, where
      it is floating), then hop1 from S into hub (b,c).
  After each case the blank is on the cell of the tile S sent, in S's reservoir.
  Continue with D_{j+1}.

A cycle closes when the blank is back in D_0 (D_0 served first, sent last).

**hop1 (S into hub h = (b,c), S = (b,J), J != c).** Let d = number of blocks strictly between
J and c. The insertion position p_d is the reservoir column of block J farthest from block c:
column offset s - 1 on right halves (p_d = (d+1)s - 1), column offset k on left halves
(p_d = (d+1)s - 1 - k); so p_d is the same for all insertions from distance d, increases
with d, and p_d >= s/2 by (P2).
The blank goes from h's reservoir into h's landing strip by a blank/tile swap (O(k)), walks
the strip to the half's end (O(s); strip tiles are reservoir tiles and only shift inside the
hub), then walks out along the half to position p_d: each step moves the next row tile one
cell toward block c; the first step moves the head into the landing strip, i.e. into hub h.
The tile T that S sends is carried inside S's reservoir to the top of that column (restoring
exit, O(s + k^2)) and swapped up into the row cell p_d (blank/tile swap across <= k rows,
O(k)); the blank ends on T's old cell.
Effect: positions 1..p of the half move one step toward the head, the head goes to hub h,
T sits at position p. Cost O(s + k^2) plus the row steps: a step is efficient for a clean
tile (it gets closer to its target column block); junk steps are charged in section 7.

**hop2 (hub h = (b,c) into D = (a,c), b != a).** The blank goes from D's reservoir into the end
of the C(c,a) half on h's side (a blank/tile swap across one row group, O(k)), walks along it
to the first cell in band b (efficient for clean tiles,
O(k) per row group crossed: O(k^2)), and the stock tile X of class (a,c) in h's reservoir is
carried into the column cell there (restoring exit, O(s + k^2)). Effect: D receives the tile
that was at the column half's end; X enters the half at band b; the blank ends on X's old
cell. D receives a class-(a,c) tile unless that end tile is junk (section 7 counts these).

**Roles of arriving tiles.** A row head dropping into a hub is home if its class is the hub,
stock if it is another class of the hub's column, floating otherwise (junk). A tile a square
receives from a column is home (floating if junk). A hop2 in case (iii) uses a stock tile.

**Parity.** Every swap uses buffers inside a reservoir, so corridor contents and their
order are exactly as described; reservoirs are only tracked by counts per class (as in
Zhong's Algorithm 4, with "target column block" for rows).

**Cost per round.** Every scheduled tile makes at most one hop1 and one hop2 in total:
O(n^2 (s + k^2)) = O(n^3/k + k^2 n^2) over the run. Bypasses: O(n) each (section 6 bounds
their number).

**Lemma 1 (stock identity).** For hub (b,c) and a class x = (x,c) with x != b, let
out_b[x](t) = clean class-x tiles from the *initial* content of R(b,c) that have dropped into
the hub by time t, new_b[x](t) = class-x tiles inserted during Transport still in R(b,c),
byp_b[x](t) = bypasses of class x at hub (b,c). Then the number of class-x stock tiles of
hub (b,c) (tiles of role stock and class x in its reservoir) is
    stock_b[x](t) = out_b[x](t) - new_b[x](t) + byp_b[x](t).
*Proof.* Stock changes only by heads of R(b,c) dropping in (+1 for class x) and services of
class x from hub (b,c) (case iii, -1). Every demand for class x at hub (b,c) (case iii or iv)
is followed by exactly one insertion of a class-x tile into R(b,c), and nothing else inserts
into R(b,c) (case ii inserts into R(b,c) only with x = b, excluded). So class-x heads of
inserted tiles = demands - new_b[x], and services = demands - byp_b[x]. []
(Tiles of other roles are never used as stock, whatever their class.)

**Corollary 1.** A bypass happens only when stock_b[x] = 0 and leaves it at 0 (the paired
insertion follows). Just before the last bypass, stock = 0, so byp = new - out <= new at that
moment. Hence
    byp_b[x] <= N_b[x] + 1,   N_b[x] := max_t new_b[x](t),
and each hub uses at most k + sum_x N_b[x] reserve tiles for bypasses; Lemma 4 shows this is
<= R.

## 5. Relocations

A **relocation** E -> Z is a blank/tile swap from the blank's cell in E to a tile t of Z's
reservoir that is a reserve tile or Z's *token* (below): O(dist(E,Z)) = O(n); only t moves,
to E, where it becomes E's token (for a cycle) or floating (for a path).
- *Cycles.* Order the cycles of the round by their first square in the snake order of the
  k x k squares (row 0 left to right, row 1 right to left, ...) and start each at that
  square. Consecutive starts increase in snake order and squares adjacent in snake order are
  adjacent on the board, so a relocation between consecutive starts costs O(s) per snake step
  plus O(s) inside the squares; one round costs O(k^2 s) in total, however many cycles there
  are: O(Delta k^2 s) = O(k^2 s^3) = O(n^3/k).
  A cycle start Z gives its token (at the very first time: a reserve tile); when Z's cycle
  closes, the next relocation brings Z a new token. So Z gives net at most one reserve tile
  for all its cycle starts.
- *Paths.* A path starts at a square Z with a dummy out-edge and ends at a square E with a
  dummy in-edge; one relocation per path, O(n), and Z gives a reserve tile. At most 2ks per
  square and I in total: O(I n) = O(k^2 n^2).
- *Round boundaries:* O(n) each, O(s^2 n) = o(n^3/k).
Reserve tiles used per square: <= R (bypasses, Lemma 4) + 2ks (paths) + 1 (tokens), which is
less than the R + 2ks + 2 available.

## 6. The in-flight bound

Fix a row half H of R(b,c), length L <= n, and classes x of column c. A tile inserted from
block distance d goes to position p_d (section 4: the same for all of them, increasing in d,
>= s/2, < L). Over the Delta rounds let
  g_d(r)   = number of insertions into H at distance d in round r (in [0,k]),
  beta_d   = (1/Delta) sum_r sum_{d' >= d} g_d'(r),
  a_{x,d}(r) = 1 if round r inserts a class-x tile into H at distance d, else 0,
  alpha_{x,d} = (1/Delta) sum_r a_{x,d}(r).
These depend on the multiset of matchings, not on their order.

**Lemma 2 (push).** A tile at position <= p leaves H after at most p + 1 insertions into H
at positions >= p. *Proof.* An insertion at position q' moves the tiles at positions
1..q' one step toward the head and outputs position 0; a tile at q <= p <= q' goes to q-1. []

Let w_d = min(Delta, ceil(2(p_d + 1)/beta_d)).

**Lemma 3 (windows).** There is an order sigma such that for every row half H, distance d,
class x and every window W of w_d + 1 consecutive rounds:
  (a) if w_d < Delta: the rounds of W, except possibly the first, contain >= p_d + 1
      insertions into H at distance >= d;
  (b) W contains at most 2 alpha_{x,d} (w_d + 1) + 30 ln n rounds inserting x into H at
      distance d.
*Proof.* Take sigma uniformly at random. For a fixed window, the matchings in it form a
uniformly random subset of size |W|, so each count is a sum over a random subset (sampling
without replacement), and the multiplicative Chernoff bounds hold for it (section 9,
"Subset Chernoff"; also Hoeffding 1963, Thm 4).
Windows at the end of the run are shorter; a window meeting the start is contained in a full
one; both only help.
(a) Terms f(pi) = sum_{d'>=d} g_d'(pi) in [0,k] (divide by k to apply the [0,1] bound), mean
    mu = w_d beta_d >= 2(p_d+1) >= s: P(sum <= mu/2) <= exp(-mu/(8k)) <= exp(-s/(8k))
    <= n^{-10} by (P1). Since insertions from distance >= d are at positions >= p_d, these
    are pushes in the sense of Lemma 2.
(b) Terms in {0,1}, mean m = alpha (w_d+1): with t = m + lambda,
    P(sum >= m + t) <= exp(-t^2/(2(m + t/3))) <= exp(-3t/8) <= exp(-3 lambda/8) <= n^{-11}
    for lambda = 30 ln n.
Events: <= Delta windows x 2k^2 halves x k distances x (1 + k classes) <= 4 k^4 s^2 <= n^6.
Union bound: failure probability <= n^{-4} < 1. []

**Lemma 4 (in flight).** Under the order of Lemma 3, for every hub (b,c):
    k + sum_x N_b[x] <= 4n(1 + ln(k Delta)) + 64 k^2 ln n + 10k <= R.
*Proof.* Fix a half H and d. If w_d < Delta, a tile inserted at distance d in round r0 has,
by Lemma 3(a) applied to the window starting at r0 and Lemma 2, left H by the end of round
r0 + w_d. So at any time the class-x tiles in H from distance d were inserted in the last
w_d + 1 rounds: at most 2 alpha_{x,d}(w_d+1) + 30 ln n by (b). If w_d = Delta the count is at
most alpha_{x,d} Delta <= alpha_{x,d} w_d. Summing over x and d, with gamma_d = sum_x alpha_{x,d}
(= the insertion rate at distance d, so gamma_d = beta_d - beta_{d+1}; w_d <= 2(p_d+1)/beta_d + 1):
  sum_{x,d} 2 alpha_{x,d}(w_d + 1) <= sum_d 2 gamma_d (2(p_d+1)/beta_d + 2)
    <= 4 L sum_d gamma_d/beta_d + 4k,
and for positive numbers, sum_d gamma_d/(gamma_d + gamma_{d+1} + ...) <= 1 + ln(total/last)
<= 1 + ln(k Delta) (nonzero rates are >= 1/Delta; total <= k). Adding 30 ln n for each of
<= k^2 pairs (x,d) per half, both halves (L_left + L_right <= n), and k: the bound. []

With Corollary 1, **no hop ever fails**, and bypasses number at most k^2 R = O(k^2 n log n),
each O(n): O(k^2 n^2 log n).

## 7. Junk and Cleanup

**Junk.** Initially the corridors hold at most 2k^2 n tiles. A junk tile in a row half only
ever moves one step toward the head per hop1 through it, until it drops into the hub: at
most n steps, i.e. at most n inefficient moves, then it is a floating tile. Same for column
halves (it drops into the served square D). So junk costs O(k^2 n^2) in total, and makes at
most k^2 n demands receive a wrong tile (hop2 delivering junk) -- those squares are owed a
class tile, which is still in flight or stock, i.e. counted below.

**State after Transport.** The misplaced tiles are: corridor contents (<= 2k^2 n), stock
(<= k^2 (n + R): initial clean row tiles plus bypass-created surplus), reserve, token and
floating tiles (<= k^2 (Q + 1) + 2k^2 n), and the tiles owed by set-aside and dummy edges
(<= k^2 Q + I). Total M = O(k^2 (n + Q)) = O(k^2 n log n).

**Cleanup.** Sort the M tiles by square. The blank is at a cell of some square Q. If some
tile of class Q lies outside Q, blank/tile swap to it: it moves into Q, the blank moves to
its old cell in square Q'. Repeat with Q'. A square other than the blank's home square that
contains the blank always has a class tile outside it (it has s^2 cells, one of them the
blank). When the blank is in its home square and that square is complete, swap to any
misplaced tile (it becomes misplaced in the home square and the cycle continues). Each step
is one blank/tile swap, O(n), and fixes a tile; at most 2M steps: O(k^2 n^2 log n).
Then every square holds exactly its own tiles (every cell, corridor cells included).

**Finish** as formalized: O(n^3/k).

## 8. Total

    O(n^3/k)         hops (s part), cycle relocations, Finish
  + O(k^2 n^2)       hops (crossings), junk, path relocations
  + O(k^2 n^2 log n) bypasses, Cleanup
With k^3 = n/ln n: O(n^(8/3) (ln n)^(1/3)).

## 9. Notes for the formalization

- **Subset Chernoff (the probabilistic input), elementary proof.** Let a_1..a_N in [0,1],
  W a uniformly random w-subset of [N], X = sum_{j in W} a_j, mu = E X = (w/N) sum a_j.
  For real lambda put y_j = e^{lambda a_j} > 0. Then E e^{lambda X} = e_w(y)/C(N,w)
  (elementary symmetric mean), and Maclaurin's inequality gives
      e_w(y)/C(N,w) <= (e_1(y)/N)^w = (mean_j e^{lambda a_j})^w,
  which is the moment generating function of the i.i.d. sum. Since e^{lambda a} <=
  1 + a(e^lambda - 1) for a in [0,1], mean_j e^{lambda a_j} <= 1 + (mu/w)(e^lambda - 1) and
  E e^{lambda X} <= exp(mu (e^lambda - 1)). Markov then gives the usual bounds:
      P(X <= (1-delta) mu) <= exp(-delta^2 mu / 2),
      P(X >= (1+delta) mu) <= exp(-delta^2 mu / (2+delta)).
  A uniformly random order of the Delta matchings restricted to a fixed window of positions
  is a uniformly random subset of that size, so this is all Lemma 3 uses (plus a union
  bound, i.e. counting permutations). For Lean: Maclaurin's inequality and the counting are
  the only new pieces. Maclaurin is not in the pinned Mathlib (checked 2026-09-26); the
  formalization proves it by induction on the number of elements with Bernoulli's inequality
  (`Hub/ChernoffMaclaurin.lean`). The cruder e_w <= (sum y)^w / w! loses a factor e^{w^2/N}: not enough.
- Probability: Lemma 3 needs only the existence of one good order. The cleanest route is a
  counting statement: for a fixed window, the number of permutations of the Delta matchings
  that make a count bad is at most n^{-10} of all of them. This is a Chernoff bound for
  uniform random subsets (hypergeometric-type sums with terms in [0,k]). Mathlib has Hoeffding
  for independent variables but (as far as I know) not the without-replacement comparison;
  alternatives: prove the subset Chernoff bound directly by the exchangeable-moment argument,
  or via Azuma on the permutation's Doob martingale (bounded differences k).
- The plan is a statement about counts only; realization of one round in moves is separate,
  with the three hop kinds and the bypass (`Hub/Simulate.lean`).
- Lemma 1 is an invariant of the count run; Lemmas 2-4 concern only the row halves' position
  dynamics, which are a function of the insertion sequence (a clean combinatorial model).
- The constants in this pen-and-paper argument are not optimized; (P1)-(P2)
  decide its threshold on n. The Lean proof uses the different parameters
  and optimized numerical budgets recorded in `LEAN_PLAN.md`.
- The initial blank may sit in a corridor: the first relocation (a blank/tile swap) moves it
  into a reservoir and puts one tile into that corridor cell, which is then junk.
- Cleanup's blank/tile swaps take their parity buffer in the blank's current square.

## 10. Evidence

pairrun.py (random order, no seeds, bypasses): bypasses per hub <= 0.78 n and in total
<= 0.22 k^2 n on random, transpose, rot90 and blockperm boards, k = 6..10, not growing;
the log factor of Lemma 4 is not visible.
