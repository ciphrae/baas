# Four-phase interface

The interfaces below are formalized in `SlidingPuzzle/Algorithm/PhaseStates.lean`
and `SlidingPuzzle/Algorithm/PhaseContracts.lean`. Their composition is proved.
`Algorithm.preparationContract` now proves `PreparationContract 1033`.
`Algorithm.transportContract` proves `TransportContract 82`.
`Algorithm.arrangeContract_bulk` proves `ArrangeContract 274`;
`arrangeContract : ArrangeContract 3277` remains as a compatibility wrapper.
`Algorithm.finishContract` proves `FinishContract 374`.
All four construction obligations are discharged.

## Common parameters and quantitative requirement

All four contracts quantify over every `k ≥ 2`, with board side `n = k^4` and
the standard target. A `PhaseBudgets` value chooses four natural constants once,
independently of both `k` and the input board.

`Algorithm.BoundedPhase k C pre post` requires, for every board `B` satisfying
`pre B`, an endpoint `D` and an actual `Path B D` such that `post D` and
`p.inefficientMoves ≤ C*k^11`. A bound on all moves is sufficient through
`BoundedPhase.of_length_bound`. Transport uses the finer inefficient-move
analysis: long monotone slides are efficient after leaving the target interval.

Invariants are required at phase boundaries. A path may temporarily disturb them.
Global reachability is carried in each boundary state and follows from the
initial reachability witness and the constructed path.

## Preconditions and postconditions

State predicates are in `SlidingPuzzle.Partition`; contracts are in
`SlidingPuzzle.Algorithm`.

| Contract | Precondition | Postcondition |
| --- | --- | --- |
| `PreparationContract` | `Reachable B` | `Prepared hk D`: reachable, `Clear`, and `LastRepresentatives` |
| `TransportContract` | `Prepared hk B` | `Transported hk D`: reachable, `Clear`, `ReservoirSorted`, and blank in the last reservoir |
| `ArrangeContract` | `Transported hk B` | `Arranged hk D`: reachable, `SquaresSorted`, and blank in the last square |
| `FinishContract` | `Arranged hk B` | `D = target (k^4)` |

- `Clear`: horizontal region `H_i` contains only group `i`; vertical region
  `V_i,j` contains only group `j`. These regions contain no blank.
- `LastRepresentatives`: `reservoirCount B (lastGroup k hk) j > 0` for every
  nonfinal group `j`. This condition is consumed by transport and is not required
  at its endpoint.
- `ReservoirSorted`: every nonblank tile in reservoir `R_i` belongs to group `i`.
- `SquaresSorted`: every nonblank tile in square `i` belongs to group `i`.
  It does not mean those tiles are already in their individual target cells.
- Every target group excludes zero. Blank location has its own condition.

`squaresSorted_iff_positions` proves that the cell-based square condition is
equivalent to every label in target group `i` actually being located in square
`i`. No reverse containment assumption is left to the finishing implementation.

Arrangement need not preserve `Clear`: moving corridor tiles into their own
squares is precisely its purpose. Finish may cross square boundaries for access
and parity repairs; independent square preservation is not an imposed invariant.

## Blank location and parity

`Prepared.blank_in_reservoir` derives blank membership in some reservoir from
`Clear`. `clear_reservoirSorted_blank_in_lastReservoir` proves that the transport
endpoint's blank is in the last reservoir from `Clear` and `ReservoirSorted`.
Thus that explicit postcondition does not add a new routing assumption.

At the Arrange/Finish boundary, `arranged_iff_parity` proves the equivalence
between `Arranged` and the conjunction of square membership, blank in the last
square, and the **global** target parity invariant (for `n ≥ 2`). It does not
postulate independent reachability of the individual squares.

Finish owns the construction of blank access, temporary tile exchanges, and
local parity adjustments, including their cost within `C_finish*k^11`. The
paper's Section 3.2 explicitly allows a temporary local target transposition;
Section 4.1's finishing paragraph refers back to that argument (printed pp. 137
and 143 of `zhong2023_additive-approximation-sliding-puzzle.pdf`). Correct group
membership alone must not be used to invoke a local solver. `target_arranged`
provides a checked basic example of the finishing input state.

## Connection to the count algorithm

`TransportPostcondition.lean` proves
`ReservoirSorted B ↔ offdiagMass (boardMatrix hk B) = 0` for `n = k^4`.
`Transported.of_count_endpoint` consequently constructs the transport boundary
state from a prepared input, an actual legal path, a clear endpoint, and zero
off-diagonal mass of that endpoint's own matrix.

An abstract count run ending in a matrix `D` is not sufficient: the physical
transport construction must connect its endpoint board to `D` and provide the
path's quantitative bound. No such construction is assumed implicitly here.

`TransportRealization.lean` now makes this connection explicit:
`TransportStepBound hk E` specifies a legal local transfer preserving `Clear`,
moving the blank to the selected source reservoir, implementing the exact count
update, and using at most `E` inefficient moves. `exists_path_of_count_run`
composes these local paths on the evolving board and proves that its actual
endpoint has the prescribed count matrix, at cost at most `t*E`.
`transportContract_of_step_bound` derives the unchanged `TransportContract C`
from local bounds `E = C*k^3`. `Transport.lean` supplies this local construction
with `C = 83`, discharging the hypothesis.

`TransportCorridors.lean` supplies a concrete part of that local construction:
`exists_horizontal_transport_slide` moves the blank to any column in a corridor
of group `i`, starting inside square `i`, with at most `k^3` inefficient moves.
It preserves nonblank corridor membership and fixes other rows. The blank is
allowed in the corridor during this operation, so the theorem does not assume
`Clear` at an impossible intermediate state.

`TransportLabels.lean` supplies the intermediate invariant `GroupEquivalent`:
temporarily regard the blank as belonging to the incoming tile's group. This
relation is preserved by the jumps and slides. At the final reservoir endpoint,
it proves both `Clear` and the exact count update of a blank/source exchange.

`Moves/Jump.lean` constructs exact opposite-color blank/tile exchanges in cropped
strips. A neighboring tile from the same group resolves parity when necessary.
Entry and horizontal travel cost at most `26*k^3` inefficient moves; exit costs
at most `26*k^3`. `TransportVerticalSchedule.lean` traverses the vertical good
intervals in either direction, using reversed row ranks for upward travel.
Only the initial interval can charge an ordinary slide; later slides are
efficient. Its exact polynomial bound is
`26*(k+2)+k^3+(k-1)*26*(k+3)`. Exit has inefficiency at most `25*k^3+1`.
Keeping both expressions exact while composing with the `26*k^3` entry bound
fits within `82*k^3` per transfer; rounding each phase first would give 83.
The count run therefore costs at most `82*k^11`.

## Completed composition

`FourPhaseContracts` packages the four uniform contracts. Its
`FourPhaseContracts.exists_solution` theorem calls each phase with exactly the
preceding phase's postcondition and proves an actual solution bound

```text
length ≤ manhattan B + 2*(C_prepare+C_transport+C_arrange+C_finish)*k^11.
```

`fourthPowerApproximation_of_phaseContracts`,
`uniformApproximation_of_phaseContracts`, and `proposition9_of_phaseContracts`
connect this bound to both final asymptotic statements. Each theorem explicitly
assumes `FourPhaseContracts`. `PhaseAssembly.lean` supplies all four fields in
`phaseContracts`, with budgets `⟨1033, 82, 3277, 374⟩`, and exports
`fourthPowerApproximation` and `uniformApproximation` without a phase hypothesis.
`Algorithm.exists_fourth_power_solution` exposes at most `3127*k^11`
inefficient moves and the solution bound `manhattan B + 6254*k^11`.
The concrete assembly obtains this sharper estimate by joining arrangement
and finishing before charging inefficiency: `(3277+747)/2=2012`, then adding
`1033+82` for preparation and transport. `BoundedPhase.exists_solution` captures
this rule, and `exists_solution_of_phase_bounds` applies it to the concrete
arrangement path and any supplied finishing length bound.
The generic composition proof uses `BoundedPhase.comp` to concatenate the
contracts before applying the exact solution identity once.

Preparation is complete in `Algorithm/Preparation.lean`:
`Partition.exists_preparation_path` constructs, from every input board, a legal
path to `Clear` and `LastRepresentatives` with length at most `1033*k^11`.
`Algorithm.preparationContract` carries reachability along that path and bounds
inefficient moves by its length, proving `PreparationContract 1033`
without any added boundary hypothesis.

The construction combines staging and representatives (`1013*k^11`), the
horizontal schedule (`12*k^10`), and the vertical schedule (`14*k^11`). Vertical
translations use chunks of width at most `k^3`; each chunk restores its blank
access route. All horizontal corridors and explicit representative positions
are preserved. The representatives remain at `(k^4-3, k^4-k^2+i)` for every
nonfinal group `i`.

Arrangement is complete in `Algorithm/Arrangement.lean`:
`Partition.exists_arrangement_path` takes `Clear` and `ReservoirSorted`, constructs
a path of length at most `274*k^11`, and proves `SquaresSorted`. It returns the
blank to its original cell and restores every reservoir cell. The contract
wrapper carries reachability and the last-reservoir blank into `Arranged`,
proving `arrangeContract_bulk : ArrangeContract 274` with unchanged predicates.
The earlier `arrangeContract : ArrangeContract 3277` is retained by weakening.

The vertical schedule exchanges `V(i,j)` with `V(j,i)` only when `i ≠ j`.
Its exact budget is `(24*(k^3-k)+2032)*(k^4-k^2)*k^4`; horizontal arrangement
costs `(24*k^3+2032)*(k^3-k^2)*k^4`. Each involution pair is exchanged once.
`arrangement_budget_le` proves their sum is at most `274*k^11` for all `k≥2`.
The leading-term interface instead retains `24*k^11+786*k^10`.

`Moves/BulkExchange.lean` implements shared staging, the paper's `θ_m` row
exchange, and reversed staging. Sets of size `m≥2`, with `2*m≤n`, cost at most
`(48*m+4064)*n`. The first placement and final boundary column contribute once
per staged row; ordinary placements use the Parberry routine. The row-exchange
word handles odd sizes through an internal reorder. Board injectivity proves
reverse set membership, and conjugation proves exact outside restoration.
Both arrangement region sizes satisfy `2*m≤k^4`, including `k=2`.

Finish is complete in `Algorithm/Finish.lean`:
`Partition.exists_finish_path` takes the original `Arranged` state and constructs
a solution of length at most `747*k^11`. No recursive subdivision is used.
First, move the blank to the global target corner within the final square.
For each nonfinal square, correct its corner by a three-cycle, borrow the blank,
solve its relabeled local board in cubic length up to a fixed transposition,
and undo access. A paired swap puts any local parity defect into two buffer
cells of the final square. All other nonfinal squares are restored exactly.
Each square costs at most `527*k^9+9352*k^4`; the schedule multiplies this
by exactly `k^2-1`. These lower-order costs are retained until the final sum.
Once the outer prefix is solved, `residual_reachable` proves that the final
square is solvable. Its cubic solution adds at most `527*k^9` moves.
Together with initial access, this is at most
`527*k^11+9352*(k^2-1)*k^4+2*k^4 ≤ 747*k^11` for `k ≥ 2`.
For a solution, `length = manhattan B + 2*inefficientMoves`, so Finish has
at most `374*k^11` inefficient moves. Its contract uses this sharper estimate
instead of charging every finishing move as inefficient.

The arbitrary-dimension reduction retains the exact outer-layer cost
`2008*(n-k^4)*n^2` until converting to real powers. With `x = n^(1/4)`,
`x < k+1` implies `n-k^4 ≤ 4*x^3`, so this adds only `8032*n^(11/4)`.
`Algorithm.optimalLength_le_manhattan_add` consequently proves
`OPT ≤ manhattan B + 14286*n^(11/4)` for every `n ≥ 16`.
`Algorithm.exists_solution_with_bound` gives a legal solution with this length
bound and at most `7143*n^(11/4)` inefficient moves.
The earlier natural-number bound in terms of `k^11` remains available as a
compatibility theorem, but the uniform approximation uses the sharper estimate.

`Proposition9Complete.lean` applies the uniform approximation to prove both final
asymptotic conclusions: `SlidingPuzzle.average_optimal_length` and
`SlidingPuzzle.gods_number`. Their conjunction is `SlidingPuzzle.proposition9`.
These theorems have no remaining phase-construction assumptions.

The newer `ParberryBounds.lean` instantiates the same interfaces with actual
constructed paths: `PrefixPathBound 616` and `CubicSolverBound 227`. Finish has
length at most `447*k^11`, so arrangement and Finish together have at most
`361*k^11` inefficient moves. Preparation contributes `645`, transport `82`,
and the resulting fourth-power coefficient is `1088` inefficient / `2176`
additive. `optimalLength_le_parberry` and `exists_solution_with_parberry_bound`
export `7104` additive and `3552` inefficient for every `n≥16`. Retaining the
size-reduction remainder until ambient size is known strengthens this further
to `3798` additive and `1899` inefficient (`exists_solution_with_parberry_uniform`).
The legacy coarse contracts above remain available.

The underlying solver proves `5*n³+O(n²)` with an explicit remainder, not the
stronger exact `CubicSolverBound 5`. The conditional `1937`/`3874` projection
therefore remains separate.

Validation: `lake build` and `lake env lean Checks/Axioms.lean`.

## Shared-staging bound update (2026-09-24)

The legacy `phaseContracts` constants above remain for compatibility. The
solving-suffix assembly now accepts `274+F≤2*S`. With the constructed Parberry
finish `F=447`, it uses `S=361`, giving fourth-power inefficiency `1088` and
additive length `2176`. Arbitrary-size uniform coefficients are `1899` and
`3798`. The final leading-term interface gives `95` for inefficiency plus
`21527*n^(5/2)`, or eventual coefficient `95.5` after absorbing that remainder.
(Cheaper transport, staging, and vertical spreading lowered this from `149.5`;
see `STATUS.md`.)
