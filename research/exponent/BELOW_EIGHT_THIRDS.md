# Below 8/3: grouped corridors with preloaded home reserves

Research snapshot: `ded24ee` (certified bound `M + 268 n^(8/3)`).
This is a proposed algorithm and a set of checked combinatorial ingredients,
**not a proved improvement to the Lean theorem**. Worktree branch:
`codex/below-eight-thirds`. Companion experiment:
`below_eight_thirds_check.py` (standard-library Python).

Follow-up: [HIERARCHY_CONDITIONAL.md](HIERARCHY_CONDITIONAL.md) gives the
many-level extension contract and a Lean-checked conditional exponent
argument. It also records an extra `O_h(k^3 b)` batch-rounding inventory
term omitted from the initial slack estimate below; this term is absorbed
by the proposed leading cost when `k^2 <= n`.

## Recommendation

Try **two routing levels first**, targeting

```
OPT <= Manhattan + O(n^(13/5)).
```

Use `k = g b` fine blocks per axis, `g ~= b ~= sqrt(k)`, and `s = n/k`.
Route first to the destination's group, then to the destination within that
group. The proposed corridor inventory drops from `O(k^2 n)` to
`O(k^(3/2) n)`. Seed uneven reserves by placing correct home tiles before
planning the run; do not obtain them by discarding uniform whole rounds.

The two main remaining mathematical jobs are a lane-weighted in-flight
bound for the new routes and a complete board embedding/operation bound.
The reserve and multihop bookkeeping below give plausible ways through
two other obstacles. None of these should be hidden inside an assumed
"hierarchical routing lemma."

## 1. What has to change

The current combined budget has the shape

```
n^3/k + k^2 n^2.
```

`Hub/AsympAccounting.lean` currently uses coefficients `42.65` and `195.3`
for these two terms in `hubBound`, with a further factor two in the final
excess-length bound. Optimizing coefficients or retuning `k` retains `8/3`.
The `k^2 n^2` terms include corridor inventory/cleanup, reserves and bypasses,
as well as crossings and dummy relocations. All must be audited.

## 2. A two-level monotone route

Partition the `k` fine columns into `g` consecutive groups of `b` columns.
For a destination column `d`, let its group be `[L,U]`.

* If source `a < L`, travel to `L`, then to `d`.
* If `a > U`, travel to `U`, then to `d`.
* If `L <= a <= U`, use only the within-group segment.

Always use the **near boundary**, not the group midpoint. Thus the segment
lengths telescope to `|a-d|` in block coordinates. Do the same vertically
after the horizontal stages. There are at most four stages per tile.
Actual cell offsets and access paths still cost local work; the telescoping
claim is about block coordinates.

For each parallel fine band, allocate:

* one coarse lane per target group, restricted to outside that group;
* `b` fine lane offsets, reused in the disjoint groups.

The sum of coarse spans is `(g-1)n`. The sum of fine spans is `(b-1)n`.
This is **span inventory**, allowing opposite directions on disjoint pieces,
before implementing endpoints, intersections and access strips. Across `k`
bands and two axes it is at most `2kn(g+b-2)`, up to embedding overhead.
The lane width per band is `O(g+b)` instead of `O(k)`.

If a vertical traversal crosses `k` bands of width `O(g+b)`, its crossing
overhead is `O(k(g+b))`. Consequently the hoped-for budget is

```
O(n^3/k + k(g+b)n^2 + n * lower_order_inventory).
```

With `g=b=sqrt(k)`, balance at `k ~= n^(2/5)`, giving exponent `13/5`.
This calculation is conditional on the inventory and operation estimates,
not evidence that the board algorithm already exists.

## 3. Multihop shortages need not cascade exponentially

An intermediate tile may be unavailable when a scheduled request is served.
Skipping the planned pipe insertion would make traffic depend on past
failures, invalidating direct reuse of the exogenous-traffic concentration
argument. Instead consider inserting a free tile marked as a **dirty
placeholder** with the requested class tag. Execute the stages backwards,
so the blank travels from the requested destination back to its source.
The first stage has its scheduled clean source tile.

At an intermediate node, for one intended class, write:

* `S`: clean stock available;
* `F`: tagged items still in incoming pipes, including placeholders;
* `D`: cumulative incoming dirty deliveries;
* `B`: cumulative missing-stock requests served with placeholders.

Start the pipes with untagged junk and the clean stock at zero. At completed
request boundaries, counting matched incoming insertions and outgoing
requests gives

```
S + F + D = B.
```

Immediately before a missing-stock request `S=0`, so the new value of `B`
is at most `F+D+1`. Hence, at every completed boundary,

```
B(v,x) <= max_t F(v,x,t) + D(v,x) + 1.
```

Every dirty incoming delivery is an earlier placeholder emission. Summing
over a layered route DAG, in which each placeholder has one successor,
gives `B_j <= N_j + B_(j-1) + C_j`, where `N_j` sums the classwise in-flight
maxima and `C_j` counts possible node/class pairs. Total failures are bounded
by a depth-weighted sum of these quantities. For fixed depth this is a
constant factor, not an exponential cascade.

The experiment implements real prefix shifts: insertion at index `p`
ejects index zero, shifts indices `1..p` towards zero, and fills index `p`.
It checks the identity and bound through chains of 2, 4 and 8 pipes.
**It assumes unlimited free placeholders.** It does not test a branching
network or prove the needed concentration bound. Each classwise maximum
must be bounded; total pipe capacity alone does not bound their sum.

## 4. Seed correct home tiles to obtain uneven reserves

Current `Hub/Run.lean` sets aside `Q'` whole matchings, creating a uniform
reserve budget. A long coarse lane may need `O(n)` reserve at its gateway;
paying that amount at all `k^2` squares loses the proposed improvement.
Simply deleting an uneven selection of demand edges is problematic too.
For example, on a directed cycle with parallel edges, a balanced removed
subgraph must have the same multiplicity at every vertex. This obstructs
that particular reserve-selection method, not uneven reserves in general.

**Alternative: prepare the home reserves physically before making the plan.**
Choose `R_v` nonblank target cells in the reservoir of each square `v` and
put their exact final tiles there. Mark those tiles free. All other
off-diagonal reservoir demand remains scheduled. This avoids deleting
off-diagonal demand edges just to obtain free tiles.

There is a simple preparation lemma using an existing primitive. To fix a
chosen target cell `a`, find its tile at `b`. If it is already correct, do
nothing. Otherwise choose a third nonblank cell `c` outside previously
protected targets and `{a,b}`. Apply the three-cycle sending the tile of
`b` to `a`, then protect `a`. Previously protected cells are preserved at
the end of every operation. `b` cannot be protected, since it contains the
distinct tile wanted at `a`. A constant number of unprotected cells suffices.

`Moves/ThreeCycleSharp.lean::exists_three_cycle_sharp` supplies each such
cycle in at most `52n` moves, restoring the blank and every other cell.
Thus at most `R = sum_v R_v` cycles suffice. To compare against the **original**
Manhattan value, conservatively charge `2 * 52nR`: the preparation can also
increase the intermediate Manhattan value by up to its length. This fits
`O(nR)`. This argument is not yet packaged as a Lean preparation theorem.

Importantly, home reserves do not create an `R_v` dummy deficit. With
`c_v` physical corridor cells in square `v` and `C_v` corridor tiles whose
target square is `v`, the demand counts satisfy

```
recv(v) - sends(v) = c_v - C_v + blank_correction(v).
```

The correct-home diagonal cancels. Consequently outgoing dummy demand is
at most `c_v + 1`, independently of the number of preloaded home reserves.
`Hub/Plan.lean::exists_rounds` already supports unequal degrees: it balances
the actual demand and pads with idle self loops. **Unequal degree does not
itself require a dummy move in every padded slot.**

This suggests choosing the `R_v` from deterministic lane-length and class
budgets before preparation, then applying concentration to the new plan.
The required statement is roughly

```
R_v >= multihop_shortage_budget(v) + local_dummy_budget(v) + O(1),
sum_v R_v = O(k^(3/2)n + k^3 log n),
R_v < usable reservoir area in v.
```

There is no proved lane-weighted shortage budget yet. In particular, do not
choose `R_v` from realized traffic and then silently assume that preparing
those reserves leaves that traffic unchanged. A geometric bound uniform
over all plans would resolve this dependency.

## 5. More levels, if two levels work

For a fixed depth `h`, use branching `b ~= k^(1/h)` and repeat near-boundary
routing inside consecutive groups. The putative lane width is `O(hb)` and
the budget, with constants allowed to depend on `h`, is

```
O_h(n^3/k + k^(1+1/h)n^2).
```

| Levels per coordinate | Optimal power of k in n | Target excess exponent |
| --- | --- | --- |
| 1 | 1/3 | 8/3 |
| 2 | 2/5 | 13/5 = 2.6 |
| 3 | 3/7 | 18/7 ~= 2.5714 |
| 4 | 4/9 | 23/9 ~= 2.5556 |

Generally the exponent is `(5h+3)/(2h+1) = 5/2 + 1/(4h+2)`.
A binary hierarchy might reach `O(n^(5/2) polylog n)`, but fixed-depth
constants cannot simply be assumed uniform when `h` grows. The earlier
Luna dyadic pilot establishes monotone abstract span decompositions, not
finite-buffer scheduling or a puzzle bound.

At a gateway serving `r` fine columns, a crude count permits `O(kr)` final
destination classes and `O(k^2/r)` gateways at that scale, hence `O(k^3)`
node/class pairs per fixed level. This is only a candidate class budget:
the actual tag definition and path merging must be checked. An additive
`O(k^3 log n)` reserve term is lower order at the fixed-depth choices above:
after multiplying by `n`, its power is `1+3h/(2h+1)`, strictly below the
target `(5h+3)/(2h+1)` by `2/(2h+1)`.

## 6. Next decisive work

1. Specify the two-level board layout, including gateway reservoirs and
   crossings; prove its total span and local capacity bounds. Avoid allocating
   a full-width lane to every final destination at a gateway.
2. Generalize segmented residence to those lanes, with planned insertions
   preserved by tags. Prove a bound on the **sum of per-class maxima** by
   incoming lane lengths plus a controlled class-count slack.
3. Package the preload lemma and extend the run invariant to the layered
   stock identity. Prove local free availability with the selected `R_v`.
4. Count blank relocations, endpoint access, dummy operations, dirty-tile
   displacement and cleanup. A routing-time estimate alone does not bound
   excess over Manhattan. Constantly many stages must cost `O(s)` local
   work per served tile, apart from the explicitly counted crossings.

Small coefficient changes cannot establish this result. Recursive Finish
alone also leaves both dominant transport terms. The two-level construction
is the most concrete candidate from this pass; seed reserves first rather
than trying to force the old uniform reserve initialization to fit it.

## Experiment scope

Run `python3 research/exponent/below_eight_thirds_check.py`.

* 422,500 endpoint routes: continuity, at most two segments, exact block
  Manhattan span; span-inventory identity for `1 <= g,b <= 12`.
* 4,186 pipeline histories / 52,384 services: stock identity and additive
  shortage bounds after every service. Includes exhaustive short histories
  and seeded burst/random histories.
* 5,456 cycle-removal vectors: balanced deletion forces uniform multiplicity.
* 1,000 home-preload trials: protected exact targets stay fixed; the demand
  imbalance remains the corridor imbalance after uneven home preparation.

These finite checks support the combinatorial model. They neither simulate
legal blank paths nor certify a new exponent, a finite-reserve scheduler,
or the probabilistic and geometric estimates still required above.
