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
  NEXT STEP: fill each row with its steady-state content (pre-simulate the row under the
  rotor insertion stream) so that stock = seeds +- fluctuation; then re-test.
- Proof direction: rotor-router (Propp machine) discrepancy bounds for the hub walk, plus
  steady-state rows. Would give seeds O(s log k): O(n^(8/3) log n), still below 11/4.
