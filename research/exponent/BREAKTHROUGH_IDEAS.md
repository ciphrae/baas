# Potential breakthroughs beyond the current bound

These are research proposals, not certified improvements. The current Lean
theorem has coefficient **776** and error scale
`n^(8/3) (ln n)^(1/3)`. The most promising proposal below changes the
in-flight analysis while retaining the present algorithm.

## 1. Follow a tile through successive distance bands: remove the logarithm?

**Priority: first. Confidence: promising proof route, with a specific missing
deterministic lemma.**

### Where the present estimate loses information

`InFlightPush.lean` only counts later insertions whose source distance is at
least the tile's *original* insertion distance. These pushes certainly move
the tile, but after it has moved nearer the hub, nearer sources can push it
too. `InFlightRound.lean` therefore gives the tile its entire lifetime at the
slow rate available at its starting position. `InFlightSum.lean` sums these
lifetimes and obtains a harmonic factor.

Fix one half, with distance bands `d = 0,...,D-1`. Write

```text
γ_d = mean insertions per round from distance d
β_j = Σ_{d ≥ j} γ_d
α_{x,d} = mean class-x insertions per round from distance d
γ_d = Σ_x α_{x,d}.
```

The current lifetime estimate is proportional to `(p_d+1)/β_d`.
Instead, aim for

```text
W_d ≤ c s Σ_{j=0}^d 1/β_j + O(d+1),
```

with the total window truncated at the number of rounds `Δ`. Only terms with
positive `β_j` matter: if `γ_d > 0`, all `β_j` for `j ≤ d` are positive.

### The proposed deterministic lemma

If a tile is at position at most `p_j`, then `s` later insertions at
distances at least `j` either remove it or bring it to position at most
`p_{j-1}`. For `j = 0`, they remove it. The insertion positions differ by `s`
between consecutive distance bands; the left-half offset only shortens the
last segment.

Apply a lower-window estimate for a segment of length `s`, then repeat at
`j-1`. Each phase can start at a round boundary. Counting the entire next
round as overhead handles insertions that occur partway through a round.
This needs a new push invariant referring to the tile's current band.

### The cancellation

The rate-weighted residence estimate has the exact identity

```text
Σ_d γ_d · s Σ_{j≤d} 1/β_j
  = s Σ_j (Σ_{d≥j} γ_d)/β_j
  = s · #{j : β_j > 0}
  ≤ sD = length of the half.
```

Thus the same style of upper-tail estimate, now for windows of length
`W_d + O(1)`, should give

```text
Σ_x max_t newCount(hub,x,t) = O(n + k² log n).
```

The ceiling and per-segment round overheads contribute `O(k²)` after
summing over classes and distances: `Σ_j β_j ≤ k²`. The upper-tail additive
term contributes `O(k² log n)` per hub. There is no leading `n log n` term.
It is essential to bound each class uniformly over time before summing;
the trivial simultaneous occupancy bound `Σ_x newCount ≤ n` is insufficient.

The existing capacity requirement has the form `s ≥ C k log n`, which
already implies `k² log n ≤ n/C`. Consequently the proposed reserve would
be `O(n)`, bypasses `O(k²n)`, and the whole cost

```text
O(n³/k + k²n²).
```

Taking `k ≍ n^(1/3)` would give **`O(n^(8/3))` with no logarithm**.
The capacity condition still holds for sufficiently large `n`. This does
not supply a numerical coefficient or preserve the current hub threshold;
the finite initial range would need separate accounting.

### What to prove or try first

1. Prove the segment evacuation lemma on `IGhost`, independently of all
   board geometry.
2. Define cumulative windows from the segment lengths. Handle zero traffic,
   a cumulative window exceeding `Δ`, and end-of-run truncation explicitly.
3. Reuse the lower Chernoff argument with required pushes `s` instead of
   `p_d+1`. Apply the upper argument once per `(H,d,x)` cumulative window,
   rather than once per stage; the count of event types should remain of
   the current polynomial order.
4. Replace the harmonic sum lemma with the finite-sum identity above, and
   feed the new reserve into the existing stock identity and cleanup proof.

A scratch check enumerated all `3^7` insertion-distance sequences for an
abstract half with three segments of length two. It checked 15,309 inserted
tile histories, including 5,193 finite proposed segment deadlines, with no
counterexample. The weighted identity was also checked with exact rational
arithmetic on uniform, geometric, and sparse rate vectors. These checks
support the mechanism; they do not establish the round-window theorem.

## 2. Replace exact three-cycles with operations that preserve region counts

**Priority: second for improving the constant. Confidence: good geometric
motivation; construction and constants are open.**

The board interface `Rel` remembers corridor entries and region counts.
`KeepKey` allows arbitrary permutations inside a region. However,
`insert_by_cycle` uses a primitive restoring every cell except three, and
the current jump similarly performs an exact local three-cycle. The `52s`
charge buys more restoration than the interface needs.

Try a direct primitive with this contract: place a requested region tile at
an insertion or jump port, preserve other regions and all protected corridor
entries, and leave the blank anywhere suitable in the reservoir. Other
tiles of that region may be shuffled. Route the chosen tile through the
reservoir rectangle and use short strip jumps to access the landing strip
or own-column piece. This explicitly addresses the obstacle noted in
`OPTIMIZATION_IDEAS.md`: the requested tile need not start in the rectangle.

For an insertion, the tile temporarily sent into the corridor by the entry
jump can be returned with a short jump before the final insertion. For the
current three-jump relocation, keep that outer construction and replace
only the local positioning of the selected tile in the target square.

The goal is a one-way placement cost plus blank access, without reversing
the whole staging path. Existing Parberry placement and reservoir-walk
lemmas are plausible ingredients. Exact costs such as `10s` or `20s` are
targets to investigate, not proved bounds. Start with tiles already in the
core, then prove the thin appendage cases while restoring crossed corridors.

This could lower the hop and relocation coefficients substantially. It
would not automatically lower the global cleanup three-cycle cost. Also,
the cubic fallback is already close to 776 at the current switch point;
a smaller uniform constant needs a lower hub threshold or better fallback.

## 3. Batch reservoir preparation instead of selecting each tile from scratch

**Priority: exploratory constant improvement. Confidence: medium-low.**

The complete sequence of scheduled outgoing classes is known before the
run. Prepare those tiles in extraction order once, then feed them through
ports or queues. A local arrangement costs `O(s³)` per square, hence
`O(n³/k)` overall. It might replace much of the repeated `52s` placement
cost on `Θ(n²)` operations with a substantially cheaper scan or queue
advance. This is another way to exploit the freedom to permute a region.

The hard case is stock: it arrives during the run and must later be selected
by class. Use separate space for prearranged scheduled tiles and dynamic
stock, or prepare batches of `Θ(ks)` tiles so the ports can be replenished.
Prove a total bound on reshuffling and blank access; simply sorting the
initial reservoir is not enough. The setup must include scheduled tiles
in the region's thin appendages and preserve corridor contents.

## 4. Choose balanced rounds as well as ordering them

**Priority: alternative to the first proposal, especially for the threshold.
Confidence: open scheduling problem.**

The current construction chooses an arbitrary perfect-matching
decomposition and obtains a useful ordering by concentration. There is
also freedom in the decomposition itself. Try to split the demand graph
recursively into regular subgraphs while balancing the traffic seen by
each half, distance threshold, and class. Alternating-cycle switches are
the natural operations for preserving sender and receiver degrees.

A deliberately generous target, at `s ≍ k²`, is a schedule with all-window
discrepancy

```text
O(k²) for each tail push count g_{≥d},
O(k)  for each class/distance insertion count a_{x,d}.
```

Together with segmented residence times, the first bound would allow a
capacity requirement `s ≥ Ck²` independent of `log n`. Summing the second
over `O(k²)` class/distance pairs gives `O(k³) = O(n)` reserve. These are
targets, not assertions that such schedules always exist.

This differs from the historical MaxWeight experiments: keep the present
own-sender pairing and its stock identity, and change only how the fixed
rounds are built and ordered. First seek a counterexample on small demand
matrices. Balancing separate classes is insufficient unless the same rounds
also satisfy the matching and push constraints.

## 5. Hierarchical corridors: a possible route below exponent 8/3

**Priority: high-risk research. Confidence: low; a different layout is needed.**

The present balance is between `n³/k` local work and `k²n²` corridor-related
work. Improving constants or eliminating the logarithm leaves this balance
at exponent `8/3`.

Instead of one lane per target block in every band, try lanes indexed by
levels of a binary partition of the destination coordinate. Tiles cross a
separator only when their source and target lie on opposite sides, then
continue in the relevant child interval. Local buffers perform the choice
of the next branch. Using two child lanes per interval would occupy
`O(n)` cells per level per band, or `O(kn log k)` cells across the board,
rather than `O(k²n)`.

If one could prove both an `O(s polylog k)` per-tile local cost and total
exceptional inventory `O(kn polylog k)`, the target accounting would become

```text
O(n³ polylog(k)/k + kn² polylog(k)).
```

At `k ≍ sqrt(n)` this suggests **`O(n^(5/2) polylog n)`**. This is a
conditional design target, not an analysis of an existing algorithm.

The obstacles are substantial: simultaneous horizontal/vertical crossings,
stock at branch points, blank relocations between scheduled transfers, and
parity. Routing must keep coordinate travel monotone except for charged
local work. The routing buffers must not silently restore the original
`k²n` inventory. A count-level model with adversarial traffic should come
before board-level paths or Lean work.

## Suggested order

Try the segmented push lemma first: it exposes an exact algebraic
cancellation and uses the current algorithm. Investigate the weaker local
placement contract next for constants. Keep the queue, balanced-round, and
hierarchical-layout ideas as distinct experiments so that their extra
invariants and costs can be assessed separately.
