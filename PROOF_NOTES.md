# Proof notes: Proposition 9 and the foundation interfaces

Initial audit date: 2026-09-12. Source: `zhong2023_additive-approximation-sliding-puzzle.pdf` (18 PDF pages). Printed page `p` is PDF page `p - 128`. The initial audit distinguishes mathematical derivations and finite diagnostics from Lean-checked results. Subsequent dated checkpoints record completed formal proofs; the 2026-09-21 checkpoint completes Transport and Proposition 9.

## Source references and conventions

| Paper location | Foundation requirement |
| --- | --- |
| Definition 1, printed p. 130 / PDF p. 2 | Coordinates are zero based; zero denotes the unique blank. The paper's broad board definition permits repeated nonzero entries, but the standard puzzle has distinct labels. Boards represented as equivalences specialize to the standard puzzle correctly. |
| Definitions 2-3 and Table 1, p. 131 / PDF p. 3 | A move moves one tile into the blank; U/D/L/R name the tile's direction, opposite to the blank's direction. The standard target is `BT(x,y) = (n*x+y+1) mod n^2`, with blank at `(n-1,n-1)`. |
| Definition 7 and Proposition 3, p. 132 / PDF p. 4 | The orbit is defined through legal move sequences. Proposition 3 states both directions of the permutation-sign/blank-color solvability criterion. An invariant alone supplies only necessity. |
| Definition 9 and Proposition 5, p. 134 / PDF p. 6 | The potential decreases by at most one per move. The solution upper bound has **twice** the number of inefficient moves. |
| Definition 11, equation (2), p. 138 / PDF p. 10 | Manhattan distance sums labels `1,...,n^2-1`; the blank is excluded. The preceding reference to an `n x 2` puzzle is a prose typo; the definition and section concern square boards. |
| Section 5, p. 144 / PDF p. 16 | Average and maximum range over the target's reachable orbit. The three finite upper bounds printed with `+ alpha` must use `+ 2*alpha` when alpha counts inefficient moves. |
| Proposition 9, p. 145 / PDF p. 17 | Uses the uniform Manhattan mean and reachable maximum lower bound cited from Parberry [2], then a center-based maximum upper bound. Neither citation is a substitute for a formal proof. |

PDF pages 3, 4, 6, 10, 16, and 17 were rendered and visually inspected to confirm notation and displayed formulas. The original Parberry paper was not inspected in this audit; the derivations below are proposed independent replacements for the two cited estimates.

## Exact path accounting and the factor two

For Manhattan distance excluding the blank, one legal move changes exactly one summand. Its integer distance changes by exactly `+1` or `-1`. Along any legal path from `B` to `B'`, let `u` count increasing moves and `d` count decreasing moves. Then

```text
length = u+d
D(B')-D(B) = u-d
length + D(B') = D(B) + 2*u.
```

For a solution, `D(B')=0`, yielding `length = D(B)+2*u` and `D(B) <= OPT(B)`. The arbitrary-endpoint form is useful for concatenation and for the general-size prefix in package F. Natural-number subtraction should not be used to express the signed one-step change without an appropriate case split or cast.

There is an elementary counterexample to the printed `+ alpha` bound in Section 5 when interpreted as a bound on the produced solution length: start at the target, make one legal move, and immediately reverse it. The solution has length 2, initial Manhattan 0, and exactly one inefficient move. Thus `SOL <= D+alpha` fails for this sequence. This does not challenge the Big-O statement: a fixed factor two is absorbed there.

For the paper's more general real potential, the reverse legal move also gives an upper bound of one on the change. That suffices for Proposition 5's inequality; the exact identity above is specific to the Manhattan `+1/-1` property.

## Mean Manhattan candidate: independently verified derivation

Write `N=n^2`, with `n >= 2`. Fix a nonblank label `t` and a cell `p`. Among all boards with `t` at `p`, swap two distinct nonblank labels other than `t`. They exist even at `n=2`, because there are three nonblank labels. This fixed-point-free involution preserves `t`'s position and the blank's position and reverses the relative permutation sign. **Assuming the full solvability criterion**, it interchanges reachable and unreachable boards in this fiber. Since the fiber contains `(N-1)!` boards, exactly half are reachable, independently of `p`. Consequently every nonblank tile has a uniform position in the reachable orbit. This argument needs no independence between tile positions.

For the distance sum, with `x,u` ranging over `0,...,n-1`,

```text
sum_(x,u) |x-u| = 2*sum_(d=1)^(n-1) d*(n-d) = (n^3-n)/3.
```

Summing the expected contribution over *all* target cells gives `(2/3)*(n^3-n)`: in two dimensions, each coordinate contributes the preceding double sum. The corner target cell reserved for zero contributes `n-1`, since the expected distance of a uniform cell from `(n-1,n-1)` is `n-1`. Remove that cell's contribution. The candidate in package C is therefore correct as a mathematical consequence of uniform marginals:

```text
averageManhattan n = (2/3)*n^3 - (5/3)*n + 1.
```

In particular the error is at most `(5/3)*n` for `n>=2`, stronger than the requested `O(n^2)` bound. The unresolved formal work is orbit sufficiency, finite fiber counting, sum exchange, polynomial sums, and casts/division. Do not export the exact identity as unconditional until these are proved.

## Half-turn lower bound: parity repair is unnecessary for square boards

The plan suggests correcting the half-turn by swapping two tiles if needed. For the square boards in Proposition 9, the half-turn already has the correct solvability parity for every `n>=2`.

Let `h(x,y)=(n-1-x,n-1-y)` and put `BH(p)=BT(h(p))`. Its blank is at `(0,0)`. The sum of initial and target blank coordinates is `2*(n-1)`, which is even. The permutation `h` is a product of disjoint transpositions:

* If `n` is even, there are `n^2/2` transpositions. Writing `n=2k` shows this number is `2*k^2`, even.
* If `n` is odd, the center is fixed and there are `(n^2-1)/2` transpositions. Writing `n=2k+1` shows this number is `2*k*(k+1)`, even.

The relative tile permutation is conjugate to this cell permutation, hence also even. **Once Proposition 3 sufficiency is formalized**, `BH` is reachable. Without sufficiency or an explicit legal construction, the parity computation alone is not a reachability proof.

Every cell crosses the center under the half-turn, so its all-label distance sum is `4*n*sum_x |x-(n-1)/2|`. Remove the blank's distance `2*(n-1)`. This gives

```text
D(BH) = n^3 - 2*n + 2       if n is even;
D(BH) = n^3 - 3*n + 2       if n is odd.
```

Therefore `max_reachable D >= n^3 - 3*n + 2`, an `O(n)` error. This is a simplification of package C, not a counterexample to its more cautious repair route. It should replace that branch once the parity and distance formulas are proved.

## Maximum upper bound

For `c=(n-1)/2`, apply `|x-x'| <= |x-c|+|x'-c|` in both coordinates to each nonblank tile. Add the nonnegative missing blank terms in the current and target boards. Since both boards are bijections on the cells, this yields

```text
D(B) <= 4*n*sum_(x=0)^(n-1) |x-c|.
```

The one-dimensional sum is `n^2/4` for even `n`, and `(n^2-1)/4` for odd `n`. Thus the displayed upper bound equals `n^3` or `n^3-n`, respectively. In particular `D(B)<=n^3` for every board, regardless of reachability. This validates package C's candidate, including its coefficients. It is an upper bound, not a claim that the reachable maximum attains it.

## Exhaustive small-board diagnostics

Breadth-first search from the standard target was run on 2026-09-12 using only swaps of zero with an orthogonally adjacent cell. Distances are therefore shortest legal lengths. These are finite diagnostic results from ordinary Python, **not Lean proofs**.

| n | Reachable boards | Mean D | Maximum D | Mean OPT | Maximum OPT | Half-turn D | Half-turn OPT |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 12 | 3 | 6 | 3 | 6 | 6 | 6 |
| 3 | 181440 | 14 | 22 | 249167/11340 | 31 | 20 | 28 |

Tile 1 appeared at every position exactly 3 times for `n=2` and 20160 times for `n=3`. Both half-turn boards were reached. The two mean values match the exact candidate. The `n=3` half-turn is not a maximizer of Manhattan distance, which is harmless for the lower bound.

Reproduce the main table with the following standalone Python program; no puzzle libraries or external data are needed:

```python
from collections import deque
from fractions import Fraction

for n in (2, 3):
    N = n*n
    target = tuple(range(1, N)) + (0,)
    goal = {t: divmod(j, n) for j, t in enumerate(target)}
    def manhattan(b):
        return sum(abs(j//n-goal[t][0]) + abs(j%n-goal[t][1])
                   for j, t in enumerate(b) if t)
    neighbors = {j: [k for k in range(N)
                     if abs(j//n-k//n) + abs(j%n-k%n) == 1]
                 for j in range(N)}
    distances = {target: 0}
    queue = deque([target])
    while queue:
        b = queue.popleft()
        z = b.index(0)
        for k in neighbors[z]:
            c = list(b)
            c[z], c[k] = c[k], c[z]
            c = tuple(c)
            if c not in distances:
                distances[c] = distances[b] + 1
                queue.append(c)
    potentials = [manhattan(b) for b in distances]
    half_turn = tuple(reversed(target))
    print(n, len(distances), Fraction(sum(potentials), len(distances)),
          max(potentials), Fraction(sum(distances.values()), len(distances)),
          max(distances.values()), manhattan(half_turn),
          distances.get(half_turn))
```

## Obligations that this audit does not discharge

1. Prove the complete reachability criterion or a sufficient constructive alternative. Both the mean and half-turn route currently depend on sufficiency.
2. Prove the potential and statistics interfaces in Lean, including the exact factor-two identity and correct distribution over the reachable orbit.
3. Formalize the finite counting and arithmetic above; small-size enumeration does not establish their general statements.
4. Construct and verify the uniform `OPT <= D + C*n^(11/4)` bound, including all fourth-power algorithm phases and the reduction to arbitrary dimensions. A mere additive `SOL <= OPT+E` theorem does not by itself supply this stronger potential-based bound.
5. Account for blank membership in Section 4.1's region invariants and for potential change during the general-size prefix, as already required by the plan. These algorithm details were not independently audited here.
6. Instantiate the final asymptotic assembly with concrete proved puzzle results. Conditional assembly or the handwritten derivations in these notes are not completion of Proposition 9.

## Lean progress following the audit (2026-09-13)

The distinction above between handwritten derivations and checked results remains
important. The following pieces are now proved in the project:

- `Path.length_add_manhattan` and `Path.solution_length` certify the exact factor-two
  identity; `manhattan_le_optimalLength` certifies its shortest-path consequence.
- `target_apply_val` and `target_bottomRight` verify the paper's target convention.
- `midpointDeviation_exact` and `manhattan_le_cube` certify the maximum **upper**
  bound. The implementation uses the integer midpoint `n / 2`, rather than the
  paper's real midpoint `(n-1)/2`. Their sums of absolute deviations agree: for
  even sizes either middle location gives the same sum, and for odd sizes the
  midpoints coincide. The proof directly establishes
  `4 * midpointDeviation n + n % 2 = n*n` by a two-step recurrence, avoiding
  real absolute-value case splits. This is an equivalent replacement for the
  printed center calculation, not an assumption about a missing library lemma.
- `Path.prefix_solution_bound` proves the finite general-size prefix accounting,
  including twice the prefix length. `exists_fourth_power_dimension` and
  `outer_layer_budget_le` prove the dimension choice and the polynomial budget
  conversion. They do not construct the outer-layer placement path.
- `conditional_proposition9` proves the two asymptotic conclusions **assuming**
  the board-uniform approximation and the mean/maximum Manhattan error bounds.
  The main missing mathematical dependencies have not been discharged by naming
  or proving this conditional theorem.

The sharper exact mean/half-turn formulas discussed above remain optional
mathematical targets. The required mean and reachable maximum O(n²) errors are
now certified by `Bridge/Statistics.lean`.

The subsequent local/parity modules also compile: `exists_path_cycle` gives an
actual length-four path and `cycle_rotate` proves its tile permutation;
`reachable_boardSign_mul_colorSign` establishes the necessary checkerboard/sign
condition. Sufficiency is now supplied by `Bridge/Reachability.lean`. The integrated
axiom check in `Checks/Axioms.lean` reports only the standard Lean logical axioms
for these exports and the conditional assembly.


## Direct partition and transport-count proof (2026-09-13)

The current definitions follow printed pp. 138–139, including vertical column
`b_i*k³+j`. No correction to that index is needed. An old neighboring phase
module's contrary comment was rejected and that module is excluded.

For every clear board, the proved corridor count for each group is
`n + k²*(k³-k)`. The group's size is `k⁶`, except that the last group excludes
the blank. Subtraction therefore gives reservoir column capacity
`(k³-k)*(k³-k²)`, with the deficit one precisely in the last column. Row deficits
track the actual blank reservoir. These are now Lean theorems, not hypotheses
introduced to make the count loop terminate.

Algorithm 4's minimum incoming-source choice and last-row invariant yield a
terminating count run. The board bridge proves at most n² transfers, assuming
Clear and the preparation representatives. This does not certify any physical
transfer, preparation path, or inefficient-move estimate.

The endpoint semantics are also checked: every positive incoming count gives a
concrete reservoir cell, and swapping its tile with the blank exactly realizes
Algorithm 4's matrix update while preserving Clear. This is a permutation
identity, not an assertion that all such transpositions are reachable. Four
specific strip swap families and blank-access paths are independently checked
in `Moves/Strips.lean`; routing the general transfer remains outstanding.


## Preparation allocation and general-size prefix (pause checkpoint)

A direct finite allocation theorem now extends any injective nonblank assignment
away from the target blank to a full target board. Disjoint target groups and
fiber cardinality inequalities construct the injection. The checked capacity
bounds cover the paper's corridor quota plus a spare for non-last groups. This
avoids importing any old local-availability diagnosis.

A concrete prefix solver alternates column placement followed by row placement,
with the row solver protecting the newly placed column. Its bound is 1004*d*n².
The order is essential for this interface: the column wrapper protects only rows
strictly above its index. Residual extraction and exact path lifting are proved;
solvability of the residual and its potential comparison remain separate work.

## Residual reduction and staging quotas (2026-09-19)

The previously open residual obligations in the general-dimension argument are
now proved. The permutation of a board with solved outer rows and columns is
the extension by identity of its residual permutation. The signs therefore
agree. Corner embedding shifts both coordinates by d, preserving checkerboard
color; parity sufficiency proves residual reachability for side length at least
two. No inference from global reachability to local reachability is left assumed.

The Manhattan sum is rewritten over cells. Solved outer cells contribute zero,
corner labels preserve the blank, and translating both positions preserves grid
distance. Thus residual potential equals global potential after the prefix.
Combining this with the bound on potential increase gives twice the prefix
length in additive overhead, not merely its length.

For `k^4 ≤ n < (k+1)^4`, a fourth-power bound `D + K*k^11` consequently gives
`OPT ≤ D + (K+7710720)*k^11`. The existing real-power comparison yields the
uniform approximation for every `n ≥ 16`. This discharges the general-size step
of Proposition 9; `FourthPowerApproximation` itself is still unproved.

The full A/B/C staging union has exactly `n+k²*(k³-k)` cells for every group.
The horizontal parts have disjoint column ranges; the C strips avoid the
horizontal rows and stay in the first k³ columns. Distinct groups have disjoint
staging sets, and the whole union lies in the first k³ rows or columns. These
facts justify the existing finite allocation capacities without an extra
availability hypothesis. The instantiated `exists_staging_path` fills all
these quotas simultaneously within `1004*k^11` legal moves.
Last-reservoir representatives and the translation
schedule remain separate preparation obligations.

## Phase boundary and parity audit (2026-09-19)

The phase contracts follow Section 4.1's phase list on printed p. 139, with
nonblank membership and separate blank-location fields repairing the literal
zero-exclusion issue. The transport blank field is derived from the board's
exact capacity margins once its reservoirs are sorted.

The Arrange/Finish boundary requires global reachability and correct square
membership, not independent local reachability. On printed p. 137, Section 3.2
explicitly permits a transposition of a temporary local target when needed for
parity; the finishing paragraph on printed p. 143 refers back to that method.
Consequently all local parity repair and blank-access paths, and their costs,
belong inside `FinishContract`. Assuming local reachability at this boundary
would transfer a substantive missing proof to an unjustified input hypothesis.

`arranged_iff_parity` proves that the global reachability field is exactly the
known parity condition at valid dimensions. `target_arranged` checks that the
finishing state includes the standard target. The four contracts compose with
the exact factor two for inefficient moves. These results validate the phase
interfaces; none constructs the still-missing four phases.

## Completed preparation construction (2026-09-20)

`SlidingPuzzle.Algorithm.preparationContract` proves the original first-phase
contract with constant `1039`. The stronger path theorem works for every board,
without a reachability assumption; reachability is carried by the constructed
path when the input is reachable. Both corridor families exclude the blank,
and `LastRepresentatives` is proved from explicit nonblank tile witnesses.

The quantitative construction uses `1013*k¹¹` moves for staging and reservoir
representatives, `12*k¹⁰` for the horizontal schedule, and `14*k¹¹` for vertical
spreading. Access routes are included and restored by a checked conjugation
construction. Vertical columns are shifted in at most `k` chunks of width at
most `k³`, so nearby access costs `O(k³)` per unit shift and global access is
paid only per chunk. All intermediate preservation and endpoint claims are
proved in the public board/path model. This avoids the overly crude `O(k¹²)`
estimate from paying board-wide access for each unit shift.

At this preparation checkpoint, Transport, Arrange, and Finish remained open.
The following checkpoint closes Arrangement; Proposition 9 remains conditional.


## Completed arrangement construction (2026-09-20)

`Algorithm.arrangeContract : ArrangeContract 12464` is now proved. The stronger
`Partition.exists_arrangement_path` takes only clear corridors and sorted
reservoirs, not reachability, and returns a legal path with square membership,
the original blank position, and every reservoir cell restored.

The paper's two exchange schedules are realized using generic set exchanges:
`V(i,j)` with `V(j,i)`, followed by horizontal slices indexed by row block,
row-within-block, and column block. These indices are the actual finite types
of the partition, so there is no extra inclusive endpoint from the prose.
Cardinalities are `k^3-k` and `k^3`, both at least two for `k >= 2`.
The schedules cost `6232*k^11` and `6232*k^10`, respectively.

The local mechanism differs from whole-strip staging: any three distinct
nonblank tiles can be staged at the top in `1508*n` moves, cycled in `100*n`,
and unstaged with the reverse relabeled path. Total cost is `3116*n` and every
other cell is restored. Two such cycles realize two disjoint transpositions.
For a set exchange, the first two positions are exchanged together; subsequent
positions each exchange along with a swap of the first two already-correct
positions. This preserves membership and ensures every operation has even
parity, including when the set size is odd. No single odd transposition with
a returning blank is assumed.

The finite involution schedule handles disjointness, fixed regions, cumulative
cost, and restoration. The partition cover and square uniqueness then prove
`SquaresSorted`. The original Arrange contract is discharged without adding
hypotheses or assuming any local block reachability. Transport and Finish remain
open, and Proposition 9 remains conditional.


## Completed nonrecursive Finish construction (2026-09-20)

The paper's instruction to skip recursive subdivision is implemented directly.
`Algorithm.finishContract : FinishContract 15000` solves the original `Arranged`
state. It does not assume that individual squares initially have the right
parity or contain a blank.

For each nonfinal square, first make its bottom-right tile correct using a
three-cycle. With the global blank at its target corner, shortest blank access
to this local corner leaves every other cell of the square unchanged. Replace
the corner label by zero to obtain a genuine local puzzle alphabet. The cubic
solver solves any such board up to a specified nonblank transposition: if its
parity is wrong, swap two labels, solve, and invert the relabeling. Undoing
access restores every outside cell. Pair any remaining local transposition
with a swap of two buffer tiles in the final square. This is an even operation
and solves the current square exactly while preserving all group memberships.

The full one-square bound is `2000*m^3+10000*n`, including correcting the corner,
local solving, blank access and restoration, and the optional parity repair.
At `m=k^3`, `n=k^4`, the schedule over at most `k^2` squares costs `12000*k^11`.
Once only the final square remains, the checked residual-reachability theorem
justifies its cubic solver from global reachability. The initial blank movement
and final cubic solution fit within the stated `15000*k^11` bound.

The contracts and their composition are unchanged. `PhaseAssembly.lean` now
reduces both conclusions of Proposition 9 to Transport alone. The remaining
obligation is a legal realization of the count transfers with the uniform
inefficient-move bound; no unconditional Proposition 9 theorem is claimed.


## Transport corridor estimate and legal run lifting (2026-09-20)

The local paper's Algorithm 4 (printed p. 141) and Fact 3 (printed p. 143)
separate long efficient slides from short jumps. `Moves/Corridor.lean` now
formalizes the slide estimate against the existing `manhattan` potential.
The proof constructs adjacent blank moves by induction along an embedded line.
Only the moved tile contributes to the potential difference, by
`manhattan_blank_swap_balance`. Past the target-coordinate interval, each
such tile moves one unit toward its target. Before that threshold, each move
uses one unit of the remaining inefficient-move budget.

The four directions use a horizontal/vertical coordinate choice and `Fin.rev`.
This reverses the line parameter only; it does not change the board target or
silently assume Manhattan invariance under relabeling. Both tile-group
membership and preservation outside the visited segment are proved.
`exists_horizontal_transport_slide` derives the actual horizontal phase-II
operation with budget `k^3` and allows its blank inside the corridor.

`TransportStepBound` specifies count equivalence of the endpoint rather than a
particular distant blank/tile transposition. This is deliberate: transport
slides permute corridor labels within a group, and a prescribed transposition
may violate parity. `exists_path_of_count_run` explicitly threads the real board
through local paths, maintaining its own matrix and blank reservoir, before
using count termination. The local legal-transfer hypothesis remains open.

## Completed Transport and unconditional Proposition 9 (2026-09-21)

The local legal-transfer hypothesis is now discharged by
`Algorithm.transportContract : TransportContract 184`. The count algorithm's
at most `k^8` transfers are realized as actual board paths, each with at most
`184*k^3` inefficient moves. The original phase boundaries are unchanged.

`Moves/Jump.lean` lifts the checked strip words to cropped strips containing the
actual endpoints, in all orientations. Opposite-color endpoints admit an exact
blank/tile exchange with length at most `25*(span+1)`. For vertical travel,
`exists_group_vertical_jump` handles either parity by using an adjacent tile
of the same group, when needed. The buffer may be horizontal; this permits
entry from a horizontal corridor without assuming another vertical good cell
beside the initial blank.

The intermediate `GroupEquivalent` invariant assigns the blank the incoming
group temporarily. Jumps and corridor slides preserve this filled group map,
even though `Clear` cannot hold while the blank occupies a corridor. At the
source reservoir endpoint, the invariant recovers `Clear` and proves that the
actual board's count matrix is precisely the selected Algorithm 4 update.
Corridor labels may permute within their group without altering this count.

The vertical route is a monotone schedule of good row intervals. Downward travel
uses ordinary row ranks; upward travel uses reversed ranks with the corresponding
shift of the first good band. The first ordinary slide costs at most `k^3`
inefficient moves. Once past the destination row block, every ordinary slide is
efficient. Initial access costs at most `26*(k+2)` moves, and each of at most k
horizontal-band crossings costs at most `26*(k+3)`. These bounds fit within
`132*k^3`. Entry plus horizontal travel costs `26*k^3`, and exit costs `26*k^3`,
giving the local constant 184. No independent `k^3` charge is made for every band.

The four phase constants are `1039`, `184`, `12464`, and `15000`. Exact Manhattan
accounting therefore gives the fourth-power solution bound
`length ≤ manhattan B + 57374*k^11`. The established general-size and statistical
reductions now yield `SlidingPuzzle.average_optimal_length`,
`SlidingPuzzle.gods_number`, and their conjunction `SlidingPuzzle.proposition9`
in `Proposition9Complete.lean`, without remaining algorithmic hypotheses.

Validation: the full project builds successfully. The expanded axiom audit checks
208 declarations, including both final conclusions, using only `propext`,
`Classical.choice`, and `Quot.sound`. All 25 imported Zhong source hashes match
the recorded manifest. The suggested staircase word was an informal diagnostic;
this construction uses the previously checked strip words instead.


## Tighter phase accounting (2026-09-21)

The legal constructions and phase boundary predicates are unchanged. The generic
four-phase composition now uses `BoundedPhase.comp`, followed by one application
of the exact solution identity, instead of unpacking and recombining four paths.

Arrangement retains the two schedule estimates `6232*k^11` and `6232*k^10`.
Since `k ≥ 2`, their sum is at most `9348*k^11` (previously `12464*k^11`).

Finish retains `2000*k^9+10000*k^4` per nonfinal square and counts exactly
`k^2-1` such squares. Including the final square's `2000*k^9` solver and initial
access gives an upper bound `2000*k^11+10000*k^6+2*k^4`. The inequalities
`32*k^6 ≤ k^11` and `128*k^4 ≤ k^11` bound this by `2313*k^11`.
For a solution, `2*inefficientMoves ≤ length`; hence the Finish contract needs
only `1157*k^11` inefficient moves (previously `15000*k^11`). This halving is
specific to a path ending at the target, not to an arbitrary phase path.

The four contract constants are now `1039`, `184`, `9348`, and `1157`.
`Algorithm.exists_fourth_power_solution` exposes the resulting bound of
`11728*k^11` inefficient moves and `manhattan B + 23456*k^11` total moves,
reducing the previous additive coefficient `57374` by about 59.1%.
The exponent `11/4` and the general-size prefix accounting are unchanged.

Validation: `lake build` succeeds. `lake env lean Checks/Axioms.lean` checks
210 declarations, including the new explicit bound and half-length lemma,
using only `propext`, `Classical.choice`, and `Quot.sound`.


## Direct ambient-size accounting and tighter Transport (2026-09-21)

The uniform arbitrary-dimension bound now uses the exact prefix estimate
`2008*(n-k^4)*n^2` from `optimalLength_le_fourth_power_prefix`.
Let `x = n^(1/4)`. Since `n < (k+1)^4`, we have `x < k+1`.
The nonnegative expression `(x-k)^2*(3*x^2+2*x*k+k^2)` proves
`x^4-k^4 ≤ 4*x^3*(x-k) ≤ 4*x^3`. Hence
`(n-k^4)*n^2 ≤ 4*n^(11/4)`, as formalized in
`outer_layer_budget_le_rpow`. The arbitrary-size reduction therefore adds
`8032`, instead of `7710720`, to the fourth-power coefficient. The original
natural-number bound remains available; its proof is now a short corollary of
the exact prefix estimate. The uniform approximation uses the real-power bound.

Transport traverses at most `k-1` intervening bands. Keeping the access cost
`26*(k+2)`, ordinary-slide budget `k^3`, and crossing budget
`(k-1)*26*(k+3)` until the final comparison gives `31*k^3` for vertical travel,
down from `132*k^3`. The entry/horizontal/exit contribution stays `52*k^3`,
so `transportContract` now has constant `83`, down from `184`.

The concrete four-phase constants are `1039`, `83`, `9348`, and `1157`.
The fourth-power solution now has at most `11627*k^11` inefficient moves and
length at most `manhattan B + 23254*k^11`. For every `n ≥ 16`,
`Algorithm.optimalLength_le_manhattan_add` proves
`OPT ≤ manhattan B + 31286*n^(11/4)`; `Algorithm.exists_solution_with_bound`
provides a legal solution with that length bound and at most
`15643*n^(11/4)` inefficient moves. The uniform additive coefficient falls
from `7734176` after the previous tightening to `31286`, about a 99.6% reduction.
The exponent `11/4`, size threshold, and legal puzzle operations are unchanged.

Validation: the full `lake build` succeeds, and `lake env lean Checks/Axioms.lean`
checks 215 declarations using only `propext`, `Classical.choice`, and `Quot.sound`.

## Reduced inefficiency budgets (2026-09-22)

The local cubic solver is now bounded by `803*n^3`, obtained from its exact
word estimate `502*n^3 + 1200*n^2 + 6`. The finish block consequently costs at
most `803*k^9 + 9352*k^4`; the complete finish schedule is bounded by
`1097*k^11`, giving `FinishContract 549`.

The horizontal preparation concatenation uses
`12*k^10 ≤ 6*k^11` for `k ≥ 2`, reducing the combined horizontal prefix from
`1025*k^11` to `1019*k^11`. Together with the `14*k^11` vertical schedule,
the preparation contract is now `1033`.

The resulting phase budgets are `⟨1033, 83, 9348, 549⟩`. The fourth-power
construction has additive bound `22026*k^11` and inefficient-move bound
`11013*k^11`. After the existing arbitrary-size prefix reduction, the explicit
bounds are `30058*n^(11/4)` for additive overhead and `15029*n^(11/4)` for
inefficient moves. These changes preserve the legal constructions and the
`2008*(n-k^4)*n^2` outer-prefix estimate.

## Paired arrangement schedule accounting (2026-09-22)

The finite involution schedule now charges one set exchange for each
nontrivial pair. Removing both indices from the recursive schedule leaves
exactly two fewer regions, so the generic cumulative schedule coefficient
halves from `6232` to `3116`. The vertical and horizontal arrangement bounds
are consequently `3116*k^11` and `3116*k^10`; using `k ≥ 2` gives
`ArrangeContract 4674`.

The current four-phase budgets are `⟨1033, 83, 4674, 549⟩`. Their sum is
`6339`, so the fourth-power construction has at most `6339*k^11` inefficient
moves and additive length at most `12678*k^11`. Adding the existing `8032`
general-size prefix coefficient gives `20710*n^(11/4)` and at most
`10355*n^(11/4)` inefficient moves.

Validation: `lake build SlidingPuzzle.Algorithm.PhaseAssembly` succeeds,
including all dependent construction modules.

## Fixed local top cycle (2026-09-22)

The generic `49*n` top-cycle bound can be replaced by four explicit jumps in
the fixed `2 × 3` patch. Three cost one move each; the jump from the third top
cell back to the blank below the first costs `21`, for a total of `24`. This
gives a general three-cycle cost `3022*n`, a paired-exchange cost `6044*m*n`,
and arrangement costs `3022*k^11` vertically and `3022*k^10` horizontally.
The combined arrangement contract is `4533`.

The current phase budgets are `⟨1033, 82, 4533, 512⟩`. The fourth-power
additive bound is `12320*k^11`, with `6160*k^11` inefficient moves; the
arbitrary-size bounds are `20352*n^(11/4)` additive and `10176*n^(11/4)`
inefficient moves.

## Sharper top-row cycle and propagated arrangement budget (2026-09-22)

`strip_place_four` gives a top-cycle word of length at most `48*n+4`. Since
`4 ≤ n`, this is at most `49*n`, improving the former `100*n` estimate.
Staging and reverse staging each cost `1508*n`, so a general three-cycle now
costs at most `3065*n`. The two-cycle exchange bound becomes `6130*m*n`;
the paired vertical and horizontal schedules cost `3065*k^11` and
`3065*k^10`. As `k ≥ 2`, their sum is at most `4598*k^11`.

The resulting four-phase budgets are `⟨1033, 82, 4598, 512⟩`. The
fourth-power additive bound is `12450*k^11`, with `6225*k^11` inefficient
moves. The arbitrary-size bounds are `20482*n^(11/4)` additive and
`10241*n^(11/4)` inefficient moves.

Validation: `lake build SlidingPuzzle.Algorithm.PhaseAssembly` succeeds,
including all dependent construction modules.

## Exact cubic solver accounting (2026-09-22)

The `Zhong.solveBoard` word bound contains `(n-2)` row rounds. Expanding it
without discarding those two rounds gives exactly
`502*n^3+196*n^2+6`, which is at most `552*n^3` for `n ≥ 4`.
The improved cubic estimate propagates through the local parity correction,
borrowed blank solve, block finish, and final square schedule. The finish path
now has length at most `772*k^11`, giving `FinishContract 386` by the exact
solution identity.

The concrete budgets are `⟨1033, 82, 4533, 386⟩`. Their sum is `6034`, so the
fourth-power solution has at most `6034*k^11` inefficient moves and length at
most `manhattan B + 12068*k^11`. The arbitrary-size bounds are
`20100*n^(11/4)` additive and `10050*n^(11/4)` inefficient moves.

## Larger local blocks and Parberry-scale projection (2026-09-22)

The existing checked solver has exact word bound `502*m^3+196*m^2+6`.
The finishing blocks have side `m=k^3≥8`, so this is at most `527*m^3`.
`exists_solution_cubic_large` is a separate stronger theorem for those blocks;
the global side-four theorem remains `552*m^3`. The revised finishing path costs
at most `747*k^11`, giving `FinishContract 374` and fourth-power budgets
`⟨1033,82,4533,374⟩`. The resulting explicit bounds are `6022*k^11`
inefficient moves and `manhattan B+12044*k^11` total moves. For arbitrary
`n≥16`, they are `10038*n^(11/4)` and `manhattan B+20076*n^(11/4)`.

Parberry's original algorithm uses a different recursive first-row/first-column
construction and proves `5*m^3+O(m^2)` moves
(https://ianparberry.com/pubs/saml.pdf). That construction is not yet a
checked solver in this repository. `Algorithm.ParberryProjection.FastFinishPath`
is an explicit conditional interface: a finishing path of `225*k^11` moves
would yield `FinishContract 113`, fourth-power inefficiency `5761*k^11`, and
arbitrary-size additive coefficient `19554` and inefficiency coefficient `9777`.
The current block overhead
accounts for `220*k^11` of that projected finishing budget, so replacing the
local cubic solver alone would lower the overall inefficiency coefficient
from `6022` to `5761` rather than toward `5`.

## Shared prefix accounting (2026-09-22)

The outer-layer path and Preparation's group staging are both built from
`exists_prefix_path`. The latter first completes the loose group quotas to a
concrete target board, then applies that same protected row/column prefix.
`PrefixPathBound P` now captures the common cost `P*d*n^2`. Its parameter is
threaded through group allocation, representative staging, horizontal
spreading, and the Preparation contract, proving `PreparationContract (P+29)`.
The arbitrary-size reduction contributes `8*P` to the real-power additive
coefficient, rather than a fixed `8032`. The existing path proves `P=1004`.

For a prospective Parberry-style protected prefix with `P=15`, the current
Finish contract gives fourth-power inefficiency coefficient `5033` and
arbitrary-size coefficients `10186` additive and `5093` inefficient moves.
Combining the same prefix with a prospective `FinishContract 113` gives
fourth-power coefficient `4772` and arbitrary-size coefficients `9664`
additive and `4832` inefficient moves. These implications are checked in
`Algorithm/SharedPrefixProjection.lean`; neither fast path construction is
claimed as unconditional. The shared prefix interface requires an arbitrary
target board with the standard blank corner, which is what group staging uses.


## Joint arrangement and finishing accounting (2026-09-22)

`BoundedPhase.exists_solution` combines an inefficient-move bound on a prefix
with an all-moves bound on a complete solving suffix. The identity
`length = manhattan + 2*inefficientMoves` makes the suffix's inefficiency at
most half its length. This avoids paying separately for potential increases
in arrangement that are undone during finishing.

The existing arrangement and finish paths cost at most `4533*k^11` and
`747*k^11` moves. Their composition is a solution with at most `2640*k^11`
inefficient moves. Preparation and transport contribute `1033+82=1115`, so
`exists_fourth_power_solution` now proves inefficiency `3755*k^11` and
additive length `7510*k^11`, improving the previous `6022` and `12044`.
For arbitrary `n≥16`, the unchanged prefix reduction adds `8032`, giving
additive coefficient `15542` and inefficient-move coefficient `7771`.
The four separate phase contracts remain valid with their original budgets;
the concrete approximation and final asymptotic theorems use the sharper
composition. No new path construction or additional hypothesis is needed.

The same composition with a conditional `225*k^11` finishing path gives
fourth-power inefficiency `3494`, additive coefficient `6988`, and arbitrary-size
coefficients `15020` and `7510`. A conditional protected prefix with `P=15`
gives arbitrary-size additive coefficient `5652` with the current finishing
path, or `5130` with the conditional faster path. The older interfaces taking
only `FinishContract` remain available, but cannot directly exploit a joint
all-moves bound. The faster prefix and finishing paths remain unproved inputs.

Validation: the full `lake build` succeeds. `lake env lean Checks/Axioms.lean`
audits 221 declarations, including the new composition lemmas and both final
conclusions, using only `propext`, `Classical.choice`, and `Quot.sound`.


## Exact active-region arrangement counts (2026-09-22)

`exists_involution_region_path_active` applies the existing involution schedule
to its nonfixed indices. This subset is closed under the involution. Pairwise
disjointness proves every omitted fixed region is preserved, so all the original
postconditions still hold, while only active regions contribute to the budget.

Vertical arrangement has `k^4-k^2` active group pairs, with exactly `k^3-k`
cells in each region. Horizontal arrangement has `k^3-k^2` active slices of
size `k^3`. Their combined move bound is

`3022*(k^4-k^2)*(k^3-k)*k^4 + 3022*(k^3-k^2)*k^7`.

`arrangement_budget_le` proves this is at most `3277*k^11` for all `k≥2`.
For `k≥6`, after converting natural subtraction to integer subtraction, the
remaining inequality is `k^7` times a nonnegative polynomial. With `t=k-6`,
that polynomial is `255*t^4+3098*t^3+9750*t^2+2736*t+1082`.
The four smaller values of `k` are checked directly. The separate arrangement
contract decreases from `4533` to `3277`.

Joining arrangement and finishing now costs `(3277+747)*k^11`, hence at most
`2012*k^11` inefficient moves. Including preparation and transport gives
`3127*k^11` inefficient moves and additive length `6254*k^11`. The arbitrary-size
bounds are `7143*n^(11/4)` inefficient moves and additive length
`14286*n^(11/4)`, for every `n≥16`. The preceding coefficients were `3755`,
`7510`, `7771`, and `15542`, respectively.

Conditional projections are tightened too: a `225*k^11` finish gives
fourth-power inefficiency `2866` and arbitrary-size coefficients `13764`
additive and `6882` inefficient moves. A protected prefix with constant `15`
gives additive coefficient `4396` with the current finish, or `3874` with the
conditional fast finish. These faster path constructions remain explicit inputs.

Validation: the full `lake build` succeeds. `lake env lean Checks/Axioms.lean`
audits 226 declarations, including the active-region wrapper, exact counts,
and arrangement budget, using only `propext`, `Classical.choice`, and `Quot.sound`.


## Constructing a proper Parberry solver (2026-09-23)

The original paper, Ian Parberry, *A Real-Time Algorithm for the (n²−1)-Puzzle*,
Theorem 1 and its proof (https://ianparberry.com/pubs/saml.pdf, pp. 3–4), states
`5*n^3+O(n^2)` and analyzes a first-row/first-column routine. Its layer estimate
is `15*n^2−24*n+19`. The reused Zhong module bearing Parberry's name does not
establish that constant: its general strip-placement gadgets give the much
larger checked solver coefficient currently used here.

This pass begins the actual efficient construction, rather than treating fast
Finish as an independent input:

- `Parberry/Diagonal.lean` defines an executable six-move northwest diagonal
  word, proves its legality and tile/blank effect, and repeats it at exactly
  six moves per diagonal unit. The entire trace is confined to its stated
  rectangle; the public legal-path theorem preserves everything outside it.
- `Parberry/Transport.lean` combines these diagonals with the checked five-move
  straight walk. Its southeast placement sector includes initial blank routing
  without touching the distinguished tile, preserves completed rows and the
  current row's prefix, and parks the blank for the next placement. Its exact
  word cost is `8*d+6*v+11`, which meets the paper's per-tile budget under the
  stated sector bounds. The continuation below completes the other ordinary
  tile-location sectors.
- `Parberry/RowEnd.lean` proves a four-move rotation that solves the terminal
  pair once those two labels are staged in the right-hand column of a 2×2
  patch. This theorem does not assume or supply the pair-staging algorithm.
- `Parberry/Reduction.lean` checks the two-by-two base (at most six moves) and
  all recursion, residual reachability, and path lifting. The sole input is
  `LayerPathBound`: an actual path solving the first row and column with
  `length+15*n ≤ 15*n^2+5` for every `n≥3`, including arbitrary input parity.
  This is the difference between `5*n^3` and `5*(n−1)^3`; the paper's layer
  estimate implies it. The result is conditional on constructing this layer.
- `Parberry/Prefix.lean` iterates the same layer on shrinking residual squares
  and relabels arbitrary target boards, proving `PrefixPathBound 15` from
  exactly the same `LayerPathBound`. This does not follow from a black-box
  cubic solver alone; it uses the stronger protected-layer construction.

The existing local parity correction, borrowed-blank solving, block finishing,
nonfinal-square schedule, and residual finishing now accept `CubicSolverBound K`.
Their former names remain specializations to the checked coefficient `527`.
`exists_finish_path_of_solver` proves total finish cost `(K+220)*k^11`.
Consequently `fastFinishPath_of_cubicSolver` derives the `225*k^11` finishing
path from a genuine coefficient-five solver, with no additional finishing
assumption. Its arbitrary-size consequences remain `13764` additive and `6882`
inefficient moves until that solver is constructed.

A completed `LayerPathBound` would discharge the prefix and solver inputs
simultaneously. `optimalLength_le_of_parberry_layer` and
`exists_solution_of_parberry_layer` then give arbitrary-size coefficients
`3874` additive and `1937` inefficient moves. These are explicitly conditional.
The remaining layer obligation is not imported as an axiom, and no `sorry`
represents it.

The continuation constructs all ordinary placement cases:

- `Wide.lean` transposes diagonal/straight transport, with separate blank
  navigation that stays below the protected row.
- `NearDiagonal.lean` handles equal displacements and the adjacent diagonal
  sector. `Small.lean` verifies the short insertion words directly.
- `TopRow.lean` handles a tile already in the unfinished target row;
  `RightPlacement.lean` assembles every source on or to the right of its target.
- `Reflection.lean` and `West.lean` keep reflected transport below the protected
  row until the final insertion. `LeftPlacement.lean` completes every ordinary
  source location. Its only geometric exclusion is that the tile cannot be the
  blank or lie in the already solved prefix.
- `RowPrefix.lean` obtains the required tile through the board inverse and
  proves those exclusions from target correctness. The resulting induction is
  an actual legal path, not an assumed sequence of favorable source positions.
- `RowBudget.lean` proves `4*columnSavings n ≤ n² ≤ 4*columnSavings n+1` by a
  two-step recurrence. Summation gives
  `2*rowPrefixBudget n d+14*n ≤ 15*n²+1` for `d+1≤n`.
- `RowSolve.lean` constructs a complete protected row for `n≥4`, with at least
  two rows below it. The first and final two columns use the existing concrete
  `Zhong.placeStep`/`solveRowAux` routines; blank normalization costs `2*n`.
  The final theorem is `2*length ≤ 15*n²+3002*n+1`, preserving every earlier row.
  Its leading coefficient is `15/2`; the coarse boundary routine contributes
  only a linear remainder.

The next continuation completes the column and recursion:

- `RectPlacement.lean` and `RectRow.lean` extend the placement and row proofs to
  height-`n`, width-`m≤n` rectangles, keeping the same height-based budget.
- `Rect.exists_applicable_word` deletes inactive moves while preserving the
  induced permutation and not increasing length. This matters at a cropped
  boundary: an inactive local move could otherwise become active globally.
- `RectEmbedding.lean` derives the rectangular board by restricting the
  target-relative permutation, and lifts applicable words with their labels
  and all outside cells preserved.
- `ColumnSolve.lean` uses the embedding `(i,j) ↦ (j+1,i)` for the transposed
  rectangle below the solved first row. It proves legal move transport and
  preservation of the blank label, then solves the first column without
  disturbing that row.
- `Solver.lean` constructs a layer of length at most `15*n²+3002*n+1` for
  every `n≥5`, with arbitrary input parity. Recursion uses the checked
  four-by-four bound `502*4³+196*4²+6=35270`. The polynomial
  `10*n³+3017*n²+3009*n+9592` equals twice that base cost at four; its difference
  between `n` and `n−1` is exactly twice the constructed layer budget. Thus
  `exists_solution_cubic_aux` proves
  `2*length ≤ 10*n³+3017*n²+3009*n+9592` for every reachable board with `n≥4`.
  The simpler public bound is `5*n³+1509*n²+1505*n+4796`.

This is an unconditional construction with the paper's `5*n³+O(n²)` move-count
form. The boundary and base algorithms differ from the paper's sharper choices;
the exact lower-order polynomial and real-time implementation claim from the
paper are not formalized. In particular this theorem is not an exact `5*n³`
bound and does not discharge the stronger `LayerPathBound`.

`ConstructedPrefix.lean` also proves prefix cost `(15*n²+3002*n+1)*d`, including
arbitrary target labels by relabeling. This supplies `PrefixPathBound 616`.
The full solver supplies `CubicSolverBound 227` for sides at least eight.
`ParberryBounds.lean` consequently gives an unconditional `447*k^11` Finish,
`2589*k^11` fourth-power inefficiency, and `5178*k^11` additive length. With
the shared prefix, the arbitrary-size constants become `5053` inefficient and
`10106` additive for `n≥16`. The sharper `1937`/`3874` results remain conditional
on the original exact layer budget. No custom axiom or proof placeholder is
used for the newly constructed solver or bounds.

Validation of the completed leading-five construction: `lake build` succeeds
(8841 jobs); the expanded axiom audit checks 315 declarations and reports only
`propext`, `Classical.choice`, and `Quot.sound`. The new source scan finds no
proof placeholders or custom axioms. Imported Zhong files were not edited.


## Keeping the size-reduction remainder separate (2026-09-24)

The previous arbitrary-size inefficiency charge `4*616=2464` used a prefix
constant chosen to cover residual sides as small as five. For dimension
reduction, retain the constructed layer polynomial instead. With
`d=n-k^4`, the prefix length and hence its inefficiency contribution are at most

```text
(15*n² + 3002*n + 1)*d.
```

`Dimension.outer_layer_width_le_rpow` proves `d ≤ 4*n^(3/4)` directly in the
ambient dimension. Consequently `Algorithm.parberry_reduction_budget` proves

```text
prefix contribution ≤ 60*n^(11/4) + 12008*n^(7/4) + 4*n^(3/4).
```

Thus the leading size-reduction inefficiency coefficient is 60, even below the
suggested estimate 80. In fourth-root notation this is `60*k^11+O(k^10)`;
expanding `n < (k+1)^4` introduces the order-ten term. The factor two in the
additive length overhead disappears when converting back to inefficiency.
No claim that the prefix itself has at most half its length in inefficient
moves is needed.

Keeping the fourth-power bound unchanged, the new unconditional legal-witness
theorem `exists_solution_with_parberry_lower_order` gives

```text
inefficiency ≤ 2649*n^(11/4) + 12008*n^(7/4) + 4*n^(3/4),
length ≤ Manhattan + 5298*n^(11/4) + 24016*n^(7/4) + 8*n^(3/4).
```

These hold for every `n≥16`. The leading inefficiency accounting is
`645 + 82 + 1862 + 60 = 2649`; the first three contributions retain their
previous uniform estimates. For a bound without an explicit remainder,
`4*(15*n²+3002*n+1) ≤ 811*n²` at `n≥16` yields a size-reduction charge of
`811*n^(11/4)`. The companion uniform theorem therefore gives inefficiency
`3400*n^(11/4)` and additive length `6800*n^(11/4)`, improving 5053 and 10106.
The old theorems remain available unchanged.

## Leading coefficients and one lower-order envelope (2026-09-24)

The new `Algorithm/CostedConstruction.lean` generalizes the protected-prefix
and local-solver inputs to arbitrary natural-valued cost functions. Allocation,
label relabeling, blank borrowing, parity repair, square scheduling, and
preparation preserve these costs instead of first converting them to a uniform
multiple of the leading power. The board predicates and legal-path obligations
are the same as in the earlier construction. Seven preparation geometry helpers
are now public so the generalization reuses the proved geometry.

`Algorithm/LeadingBudgets.lean` separates each budget into
`leading*k^11 + remainder*k^10`. Its composition lemma adds the fields
separately. The remainder coefficients are intentionally loose; no bound on
small boards changes the leading coefficient. The checked phase budgets are:

| Phase | Quantity bounded | Leading | Order-ten remainder |
| --- | --- | ---: | ---: |
| Preparation | Inefficient moves (via length) | 23 | 3036 |
| Transport | Inefficient moves | 52 | 104 |
| Arrangement | Length | 24 | 786 |
| Finish | Length | 5 | 17164 |

Preparation consists of the `15*k^11+3002*k^7+k^3` staging prefix,
`9*k^6` representative access, `12*k^10` horizontal spreading, and the
`8*k^11+12*k^9` vertical spreading estimate. The exact transport step cost
is at most `52*k^3+26*k^2+78*k`; at most `k^8` transfers give the stated
transport budget. The arrangement polynomial is bounded by
`24*k^11+786*k^10`. Finishing is bounded before enveloping by

```text
5*k^11 + 1509*k^8 + 1505*k^5 + 4796*k^2 + 9354*k^6.
```

The complete arrangement-and-finish suffix is charged at half its combined
length. The resulting theorem preserves the half-integer leading coefficient:

```text
2*inefficiency ≤ 179*k^11 + 24230*k^10,
length ≤ Manhattan + 179*k^11 + 24230*k^10.
```

`Algorithm/LeadingBounds.lean` carries this through the arbitrary-dimension
reduction. Its `60*n^(11/4)` leading inefficiency cost adds to `179/2`, and
all lower-order powers are bounded by a single `n^(5/2)` envelope:

```text
inefficiency ≤ (299/2)*n^(11/4) + 24127*n^(5/2),
length ≤ Manhattan + 299*n^(11/4) + 48254*n^(5/2).
```

These bounds hold for every `n≥16`, uniformly in the input board. Only the final
adapter absorbs the remainder. The elementary quarter-power-gap lemma shows
that `R*n^(5/2) ≤ n^(11/4)` when `n≥R^4`. Taking `R=48254` gives eventual
inefficiency `150*n^(11/4)` and additive length `300*n^(11/4)`.
The threshold is deliberately enormous and unoptimized: it establishes the
asymptotic statement, while the two-term bounds retain useful explicit data.

`Proposition9Complete.lean` now uses `uniformApproximation_leading`. The
statement of Proposition 9 is unchanged; its approximation interface already
allows a sufficiently-large-size threshold. Existing exact uniform bounds are
preserved under their previous names. The leading coefficients here are upper
bounds extracted from current constructions, not claims of optimality.

## Whole-family arrangement construction (2026-09-24)

This supersedes the earlier generic three-cycle arrangement budgets. The paper's
Phase III exchanges sets using one access sequence, `θ_m`, and reversed access.
`Moves/BulkExchange.lean` now implements that construction with actual legal paths:

1. Stage the two families consecutively in the top row using `ShortRow.lean`.
   Ordinary placements cost at most `8*n` each. First-column and final-column
   boundary work contributes at most `1008*n` per row, separately.
2. Apply `θ_m` to the second half, putting the second family below the top row.
   All its labels are now outside the protected top row. Extend the current top
   row and those labels to a target board, then stage the second family into the
   first `m` cells of row one while preserving the full top row.
3. Route the blank to `(2,0)` and apply `θ_m` to the two staged families.
   Its checked row-one effect and outside preservation, together with board
   injectivity, prove that row zero receives exactly the other family's labels.
   No pointwise swap is required, so odd cardinalities cause no parity gap.
4. `Path.exists_unstaged` transports this set exchange back to the original
   cells and restores every outside cell and the blank exactly.

Staging costs at most `24*m*n+2020*n+6*m+2`. The complete exchange costs
`48*m*n+4040*n+18*m+6 ≤ (48*m+4064)*n`. Both arrangement set sizes obey
`2*m≤n`, even in the smallest case `k=2`, where horizontal staging fills the
whole row and exercises the boundary-column branch.

The shared schedule now abstracts the set-exchange budget (`SetExchangeBound`)
and counts each nonfixed involution pair once. Its original three-cycle wrappers
are retained, while `BulkExchangeSchedule` supplies the new construction.
The exact total is

```text
(24*(k^3-k)+2032)*(k^4-k^2)*k^4
+ (24*k^3+2032)*(k^3-k^2)*k^4.
```

It is at most `274*k^11` (check `k=2` separately; use `k≥3` otherwise).
Alternatively it is at most `24*k^11+24*k^10+2032*k^8+2032*k^7`, hence
`24*k^11+786*k^10` for `k≥2`. The final leading bound is now
`2*inefficiency ≤ 179*k^11+24230*k^10`; arbitrary dimensions give
`inefficiency ≤ 149.5*n^(11/4)+24127*n^(5/2)`.

The constructed Parberry uniform theorem names are strengthened to `1088`/`2176`
for fourth powers and `1899`/`3798` for arbitrary sides at least sixteen.
The original coarse phase package and its `3127`/`6254`, `7143`/`14286` bounds
remain available. No imported Zhong source was modified.

Validation: `lake build` passes (8847 jobs). The expanded
`lake env lean Checks/Axioms.lean` audits 367 declarations with only
`propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or new
axiom declarations were introduced.

## Half-charged transport jumps (2026-09-24)

Every transfer in Transport (Algorithm 4) begins and ends with a strip jump
across at most `k^3` cells, of length at most `25*k^3`. These jumps were
charged as if every move were inefficient. However, a jump's net effect is a
single blank/tile exchange: every other cell is restored. By
`manhattan_blank_swap_balance` and the triangle inequality, the Manhattan
potential changes by at most the exchange distance `d`. The exact identity
`length + M(end) = M(start) + 2*inefficientMoves` then gives

```text
2*inefficientMoves ≤ length + d.
```

This is `Path.two_inefficientMoves_le_of_blank_swap`. In both jumps
`d ≤ k^3`, so each costs at most `13*k^3` inefficient moves. The step bound
becomes `27*k^3+E+1`, with vertical budget `E = k^3+26*k^2+78*k-26` as before.
The Transport leading coefficient falls from `52` to `28`. This is the same
potential argument that halves the solving suffix, but applied locally: it
needs only a restored neighbourhood, not a solved endpoint.

Consequently the fourth-power bound is `2*inefficiency ≤ 131*k^11+24230*k^10`,
and for every `n≥16`

```text
inefficiency ≤ (251/2)*n^(11/4) + 24127*n^(5/2),
length ≤ Manhattan + 251*n^(11/4) + 48254*n^(5/2).
```

The eventual coefficients are `126` and `252`. The leading contributions are now
size reduction `60`, Transport `28`, Preparation `23`, and the halved
arrangement-and-finish suffix `14.5`. The same argument does not directly help
Preparation's vertical spreading: its band paths permute whole row bands, so
their Manhattan change is not small relative to their length.

## Reservoir-local transport entry and exit (2026-09-24)

This extends the previous section. The transfer contract is count-based: the
endpoint must be clear, have its blank in the target reservoir, and have the
Algorithm 4 count matrix. The pointwise `GroupEquivalent` invariant is only an
intermediate tool. So a transfer may permute tiles within a reservoir.

*Entry.* Before a transfer, the blank slides up its column to the first
reservoir row. Every move swaps two cells of the same reservoir, which preserves
`Clear` (`clear_swap_reservoirs`) and every count
(`boardMatrix_swap_same_reservoir`, from `reservoirCount_swap_balance` and
`reservoir_unique`). The count choice is re-made on the normalized board, which
has the same matrix. The entry jump then crosses only the horizontal corridor
rows, costing `O(k)`; the slide costs at most `k^3` moves.

*Exit.* Let the blank reach the vertical corridor cell `c` in the source tile's
row `R`, and let the tile `t` be in column `x` of the reservoir. Write `L` for
the reservoir's first column and choose `δ∈{0,1}` so that `c` and `(R,L+δ)`
have opposite colours. With `w=L+δ` and an adjacent reservoir helper row `H`:

1. Jump `c ↔ (R,w)`: an arbitrary reservoir tile `g` moves into the corridor.
2. Walk the blank along row `R` to `(R,x-1)`, then apply `x-1-w` five-move
   carries using row `H`; `t` ends at `(R,w+1)` with the blank at `(R,w)`.
3. Jump `(R,w) ↔ c`, returning `g` to the reservoir.
4. Move the blank from `c` to `c'=(H,c.2)`, still in the corridor.
5. Jump `c' ↔ (R,w+1)`, moving `t` into the corridor.

The parity of step 5 follows from that of step 1 because `H` and `R` differ by
one. The jumps span at most `k^2+2` columns. Steps 3 to 5 leave both corridor
cells with tiles of group `i`, so the endpoint is clear. Six swap-balance
equations show that the reservoir counts equal those of the direct exchange
`swapCells S (blank S) b`. The exit costs at most `6*k^3+69*k^2+176` moves. If
`x≤L+1`, the direct jump already costs `O(k^2)`.

The step bound is `8*k^3+E+69*k^2+13*k+189`. With the vertical budget,
Transport has leading coefficient `9`: one unit each for the entry slide,
horizontal travel, and vertical travel, and six for the exit walk and carries.
The previous route is kept for the legacy uniform contract, because its
lower-order terms are smaller at `k=2`.

The fourth-power bound is `2*inefficiency ≤ 93*k^11+24402*k^10`. For every
`n≥16`,

```text
inefficiency ≤ (213/2)*n^(11/4) + 24213*n^(5/2),
length ≤ Manhattan + 213*n^(11/4) + 48426*n^(5/2),
```

with eventual coefficients `107` and `214`. The remaining leading contributions
are size reduction `60`, Preparation `23`, the halved arrangement-and-finish
suffix `14.5`, and Transport `9`.

## Mixed staging prefix and per-column spreading (2026-09-24)

*Staging.* Every compressed staging cell lies in the first `k³` columns or the
first `k²` rows, and the representatives lie in row `k²`. The earlier prefix
solved `k³` complete layers (rows and columns), costing `15*k^11`. Solving a
single row with the rows above protected costs `2*length ≤ 15*n^2+3002*n+1`
(`exists_complete_row`). Transposing the board turns `d` such rows into `d`
columns; the relabelling argument of `parberryPrefixCost` handles the arbitrary
target. The remaining `k²+1` rows lie in the `n × (n-k³)` rectangle to the
right of the solved columns, where the checked rectangular row word applies
because its width is at most its height. The combined doubled cost is
`(k³+k²+1)*(15*k^8+3002*k^4+1)`, so staging has leading length `7.5*k^11`.

*Vertical spreading.* Column `i < k³` of a band moves to
`(i/k²)*k³ + i%k²`, a distance `(i/k²)*(k³-k²) ≤ (i/k²)*k³`. The chunked
translation therefore needs `i/k²` chunks of width `k³`, not a uniform `k`.
Pairing `i` with `k³-1-i` gives `2*Σ i/k² + k³ ≤ k^4`. Each chunk costs at most
`8*k^6+4*k^4+8*k^3`, so a band satisfies `2*length ≤ 8*k^10`, and all `k` bands
satisfy `2*length ≤ 8*k^11`.

*Doubled budgets.* `CostedPhase` bounds `2*inefficientMoves`. Preparation is
`⟨23,700⟩` and Transport `⟨18,380⟩`, so the fourth-power bound is
`2*inefficiency ≤ 70*k^11+19030*k^10`. For every `n≥16`,

```text
inefficiency ≤ 95*n^(11/4) + 21527*n^(5/2),
length ≤ Manhattan + 190*n^(11/4) + 43054*n^(5/2).
```

The remaining leading contributions are size reduction `60`, the halved
arrangement-and-finish suffix `14.5`, Preparation `11.5` (staging `7.5`,
vertical `4`), and Transport `9`. The size-reduction prefix genuinely needs `d`
complete layers, so the column-only trick does not apply there.
