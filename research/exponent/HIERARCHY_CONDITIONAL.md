# A composable hierarchy lemma and its consequences

Research, 2026-09-28. Companion Lean file: `HierarchyConditional.lean`.
This work does **not** establish a new sliding-puzzle exponent. It proves
conditional accounting consequences and identifies a stronger, reusable
routing hypothesis to pursue. See `BELOW_EIGHT_THIRDS.md` for the initial
proposal and home-reserve preparation argument.

## What can be settled before constructing two levels

A numerical theorem `OPT <= M + O(n^(13/5))` by itself does not imply bounds
for three or more levels. The useful hypothesis is a one-level extension
operation, valid for intermediate tagged traffic as well as original tiles.
It must preserve the properties below at arbitrary fixed depth.

Conditional on this operation and its move accounting, for each fixed
positive integer `h`, the target is

    OPT <= M + O_h(n^((5h+3)/(2h+1)))
        = M + O_h(n^(5/2 + 1/(4h+2))).

Consequently every fixed `epsilon > 0` gives `M + O_epsilon(n^(5/2+epsilon))`.
Neither the construction nor depth-uniform constants are asserted here.

The Lean file checks the exponent algebra, logarithmic slack absorption,
integer branching, and this epsilon implication. Its `HierarchyBudget`
premise is explicit and **unproved for the puzzle**. Separate Lean lemmas
check the quantitative induction for one-level resource increments and the
additive shortage recurrence. No axiom or `sorry` is introduced.

## 1. Use one outer matching plan at every level

Let there be `k=b^h` fine blocks per axis, with fine side `s`. Decompose the
post-preparation demand into the usual matching rounds. For each real edge
`S -> D`, fix its entire hierarchical route before ordering those rounds.
All levels use the **same permutation of those original rounds**.

A planned segment record contains its lane, insertion distance, original
source band, final destination `D`, stage, and round. It exists regardless
of whether the requested clean stock is present when served. A missing
clean tile is replaced by a dirty placeholder carrying the intended final
destination tag. Actual tile identity must not decide which records occur.

This provides two elementary facts at every depth:

1. A given final class `D` contributes at most one insertion to a particular
   lane per round: `D` has one preimage under the round's permutation, and
   its monotone route uses that lane at most once.
2. A lane gets at most `k` insertions per round. A horizontal lane belongs
   to a fixed original source-row band, containing `k` sources. A vertical
   lane belongs to a fixed final-column band, containing `k` destinations.

A gateway can therefore receive multiple requests in a round; requiring it
to receive at most one would be the wrong interface. The final destination
must remain the tag. Coarsening tags to group names would lose property 1.

These are the inputs behind `InFlightRound.sum_count_roundIns_le_one` and
`countP_half_le`. Their existing proofs use the current layout, but the
counting arguments have the same form here. The concentration events should
be union-bounded across **all** levels at once. There is no assumption that
traffic exiting a parent is an independently random input for its child.

## 2. A route extension with explicit counts

At a parent interval of `r` fine blocks, split into `b` consecutive children
of size `r/b`. For the child containing the target, move to its nearer
boundary if outside it, then recurse inside it. If already inside, skip
that segment. This uses at most `h` monotone segments per coordinate.
The sum of block-coordinate spans is exactly the endpoint distance.

At a fixed level, in each parallel fine band:

- there are `k/r` parents;
- each parent has at most `2b` directed pipe pieces;
- the sum of pipe spans is `(b-1)n` across the whole band;
- each piece supports at most `k(r/b)` final destination classes.

Across `k` parallel bands this gives, per level and coordinate,

| Quantity | Upper bound, ignoring absolute constants |
| --- | --- |
| Lane row/column offsets | `b` |
| Physical span inventory | `knb` |
| Directed lane/class pairs | `k^3` |
| Batch/window rounding inventory | `k^3 b` |

The class count follows by multiplying `2k^2 b/r` directed pieces by
`kr/b` possible classes. For the rounding count, each piece has at most
`r` distance bands and at most `k` insertions per round, so its crude
rounding contribution is `O(kr)`. Multiplying yields `O(k^3b)`.
The latter is a **candidate bound for the generalized residence proof**,
not a proved new residence theorem; it tracks the analogous round/window
rounding terms in the current proof.

This corrects an omission in the first budget, which mentioned only
`k^3 log n` as slack. The extra `k^3b` does not change the target exponent:

    n k^3 b <= k b n^2                 whenever k^2 <= n.

`rounding_inventory_absorbed` proves this inequality in Lean.

A simple embedding candidate is to reserve `hb` complete horizontal offsets
in every fine row band, indexed by (level, child index), and analogous
vertical offsets. Distinct parents reuse an offset on disjoint intervals.
Reserving even unused gaps costs `O(hknb)`, the same order as the span
count. Vertical paths can skip the reserved horizontal offsets. This could
retain square reservoir cores with side `s-O(hb)`. Proving the local move
primitives and endpoint access for this layout remains necessary.

## 3. The actual one-level extension contract

The following contract is stronger than a successful two-level experiment.
An implementation should accept an existing prefix of tagged routes and
add the next child-group stage while preserving:

**Traffic and service.** The segment records are deterministic functions of
the original matching edges. Each record is executed exactly once, whether
clean or dirty. No duplication, uncounted retry, dropped insertion, or new
random matching decomposition is allowed. Skipped stages are accounted
for in a layered DAG with a depth rank; each dirty item has one successor.

**Geometry.** The added segment is coordinate monotone at block scale.
Different parents reuse offsets without interfering. Access to the relevant
pipe and reservoir costs `O_h(s)` per stage. Crossings contribute at most
`O_h(kb)` per routed tile. Blank relocation between original matching edges
must obey the corresponding round-walk bound. These are excess-move
claims, not just packet travel-time claims.

**Residence.** For the fixed exogenous segment records, the sum of classwise
maxima of tagged in-flight items at a level is at most

    O_h(knb + k^3b + k^3 log n).

The maximum for each class may occur at a different time. Simultaneous pipe
capacity alone does not establish this sum. The desired proof adapts
segmented residence and the rate-weighted reciprocal-tail telescoping in
`InFlightSegment.lean` and `InFlightSum.lean`.

**Stocks and finite reserves.** The local identity `S+F+D=B` holds at matched
request boundaries, including the timing just before a shortage. Hence
`B_j <= B_(j-1) + A_j`, after aggregating over a layer; `A_j` includes
in-flight maxima and one unit per possible class. A deterministic local
reserve budget must be available before planning, fit in the reservoir,
and cover shortages plus outgoing dummy requests. Preload correct home
tiles using three-cycles, as described in the earlier note. Charge the
preparation against the original Manhattan value, including its possible
increase. No traffic-dependent reserve choice may be assumed unchanged by
this preparation.

**Completion.** Total stock, dirty tiles, preloaded reserves, initial junk,
and final pipe contents must be bounded by the same aggregate inventory.
Their cleanup costs `O(n)` each. Finish the local squares and include parity
and designated-cell restoration. The construction must also extend to
arbitrary board sizes with the boundary-strip cost recorded below.

The existing solver has these ideas for its specific layout. The contract
has not been proved for the proposed grouped layout.

## 4. Why the quantitative induction works

Write `H=2h` for a convenient upper bound on coordinate stages. Suppress
absolute constants in this paragraph. Per-level increments give

    width <= O(hb),
    lane inventory <= O(hknb),
    rounding inventory <= O(hk^3b),
    class slack <= O(hk^3 log n).

For shortages, put `A_j` equal to the level's in-flight and class budget.
From `B_0=0` and `B_(j+1)<=B_j+A_j`,

    B_j <= sum_(i<j) A_i,
    sum_(j=1..H) B_j <= H sum_(i<H) A_i.

Thus a bounded per-level budget incurs at most a quadratic depth factor
from this recurrence. Lean proves these statements in `shortage_prefix`,
`shortage_total`, and `shortage_uniform`. This does not bound other possible
depth dependence in the geometry or concentration constants.

With the contract's local operations and cleanup estimates, the cost is

    O_h(n^3/k + kbn^2 + nk^3b + nk^3 log n).

When `k^2<=n`, absorb the third term into the second. Substitute `b=k^(1/h)`
to obtain the `HierarchyBudget` expression. The move-accounting implication
from the physical contract to that expression is an unproved obligation;
the Lean resource lemmas do not construct paths.

## 5. Integer choices, capacity, and all board sizes

Take

    b = floor(n^(1/(2h+1))),    k = b^h.

For `n>=1` this satisfies

    n^(h/(2h+1))/2^h <= k <= n^(h/(2h+1)).

`exists_integer_branching` proves these inequalities, so the result is not
restricted to the subsequence `n=t^(2h+1)`. Branching at least two and any
fixed minimum grid size hold after increasing the threshold for fixed `h`.
For a physical board use `s=floor(n/k)` and solve the outer remainder first.
The existing `AsympBound.lean` prefix has excess `O(kn^2)`, which fits
`O(kbn^2)`. Its existing hub call must be replaced by the new construction;
this note does not claim its hypotheses apply to the new layout already.

At the balanced choice, `n/k^2` grows at least as `n^(1/(2h+1))`. Therefore
requirements such as `s >= C_h k log n` are eventually affordable for each
fixed depth. A proposed local reserve bound must still be stated and proved;
aggregate reserve area alone does not prove it fits at every gateway.

Let `a=h/(2h+1)`, `p=(5h+3)/(2h+1)`, and `delta=2/(2h+1)`. For any positive
`k` in the above bracket with lower-factor loss `Q`, Lean proves

    n^3/k + k^(1+1/h)n^2 + nk^3 log n
      <= (Q + 1 + 1/delta) n^p,       n>=1.

This uses `log n <= n^delta/delta`. Taking `Q=2^h` yields an explicit
fixed-depth coefficient. `hierarchy_budget_implies_epsilon` then proves
the conditional `5/2+epsilon` statement with constants and size threshold
allowed to depend on epsilon.

An `n^(5/2) polylog n` conclusion would additionally require controlled
constants as depth grows, compatible capacity estimates, and a sharper
integer-grid analysis if the crude `2^h` loss is too large. It does not
follow merely from the fixed-depth theorem.

## 6. What has been checked

Run:

    lake env lean research/exponent/HierarchyConditional.lean
    python3 research/exponent/hierarchy_route_check.py

The Lean file checks the conditional algebraic statements; it does not
import or modify the certified puzzle theorem.

The Python pilot checks `b=2,3,4` and `h=1,2,3,4`:

- 77,624 endpoint routes: continuity, monotonicity, at most `h` segments,
  and exact block Manhattan span;
- per-level span and class-count bounds;
- 232,872 demands from transpose, reverse and seeded random permutations:
  at most `k` insertions per physical lane per round and at most one per
  final class. Lane keys include the parallel band, avoiding aggregation
  across distinct physical lanes.

These are finite checks of the abstract construction, not legal blank-path
simulations or concentration tests.

## Next implementation target

Generalize the deterministic pipe and in-flight machinery to a lane family
with its own endpoint, length, insertion positions and class support. Keep
records indexed by the original matching plan. Establish one **parametric**
residence lemma using the two multiplicity facts above. That would settle
the probabilistic part for every fixed depth at once. Then implement the
smallest grouped board layout and discharge its geometric and reserve
obligations against the same interface.
