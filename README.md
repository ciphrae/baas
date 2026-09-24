# Sliding Puzzle formalization

This repository proves Proposition 9 in Zhixian Zhong, *Additive Approximation
Algorithms for Sliding Puzzle*, in Lean. Both asymptotic conclusions are
unconditional theorems for the reachable orbit of the standard target:
`SlidingPuzzle.average_optimal_length`, `SlidingPuzzle.gods_number`, and their
conjunction `SlidingPuzzle.proposition9`, in `Proposition9Complete.lean`.

## Reproducible build

The checked environment is Lean `4.33.1` (`leanprover/lean4:v4.33.1`) with
mathlib input tag `v4.33.1`, pinned in `lake-manifest.json` to commit
`0df444a360eaa60ab8c11dca51a86af692955474`. A normal checkout can use:

```sh
lake exe cache get
lake build
```

The current workspace was verified with `lake build`. Individual modules can
also be checked, for example `lake build SlidingPuzzle.Paths` or
`lake build SlidingPuzzle.Basic`. The root `SlidingPuzzle.lean` is the current
integration entry point; the default build includes the completed foundations,
statistical bridges, placement lemmas, and board/count transport development.

## What is formalized so far

The following declarations compile and describe the frozen core interfaces:

| Paper concept | Module and exported declarations |
| --- | --- |
| Boards, target, positions, blank, legal swaps | [`SlidingPuzzle.Basic`](SlidingPuzzle/Basic.lean): `Cell`, `Tile`, `Board`, `target`, `position`, `blank`, `swapCells`, `Step`, `manhattan` |
| Row-major target facts | [`SlidingPuzzle.Target`](SlidingPuzzle/Target.lean): `target_apply_val`, `target_bottomRight` |
| Legal paths and the reachable target orbit | [`SlidingPuzzle.Paths`](SlidingPuzzle/Paths.lean): `Path`, `Path.length`, `Path.append`, `Path.reverse`, `Reachable`, `ReachableBoard`, `targetBoard`, `exists_solution` |
| Shortest solution interface | [`SlidingPuzzle.Paths`](SlidingPuzzle/Paths.lean): `optimalLength`, `shortest_witness`, `optimalLength_le_path_length`, `optimalLength_target` |
| Manhattan one-step accounting | [`SlidingPuzzle.Manhattan`](SlidingPuzzle/Manhattan.lean): `Step.manhattan_delta`, `Step.manhattan_le`, `Path.inefficientMoves`, `Path.length_add_manhattan`, `Path.solution_length`, `manhattan_le_optimalLength` |
| Finite orbit means and maxima | [`SlidingPuzzle.Statistics`](SlidingPuzzle/Statistics.lean): `finiteMean`, `finiteMaximum`, `orbitAverageManhattan`, `orbitAverageOptimalLength`, `orbitMaximumManhattan`, `orbitGodsNumber`, and finite sandwich/attainment lemmas |
| Unconditional statistical bounds currently integrated | [`SlidingPuzzle.StatisticalBounds`](SlidingPuzzle/StatisticalBounds.lean): `averageManhattan_le_averageOptimalLength`, `maximumManhattan_le_godsNumber`, `maximumManhattan_le_cube`, `maximumManhattan_abs_error_le` |
| Executable local words and preservation | [`SlidingPuzzle.Moves.Local`](SlidingPuzzle/Moves/Local.lean): `Executes`, `Executes.exists_path`, `Executes.preserves`, `Executes.append`, `reachableAfter`, `optimalLength_le_word_then_solution` |
| Finite path accounting helpers | [`SlidingPuzzle.Algorithm.Accounting`](SlidingPuzzle/Algorithm/Accounting.lean): `Path.inefficientMoves_le_length`, `Path.manhattan_end_le`, `Path.prefix_solution_bound`, `Path.four_phase_solution_bound`, `optimalLength_le_prefix_solution` |
| Fourth-power dimension arithmetic | [`SlidingPuzzle.Algorithm.Dimension`](SlidingPuzzle/Algorithm/Dimension.lean): `fourthRoot`, `le_fourthRoot_iff`, `exists_fourth_power_dimension`, `outer_layer_budget_le` |
| General arithmetic helpers | [`SlidingPuzzle.Asymptotics`](SlidingPuzzle/Asymptotics.lean): quadratic-to-`n^(11/4)` bounds, fourth-power gap, and `k^11` comparison lemmas |
| Conditional Proposition 9 assembly | [`SlidingPuzzle.Proposition9`](SlidingPuzzle/Proposition9.lean): `UniformApproximation`, `uniform_approximation_statistics`, `conditional_average_optimal_length`, `conditional_gods_number`, `conditional_proposition9` |
| Exact staging quotas | [`SlidingPuzzle.Algorithm.Staging`](SlidingPuzzle/Algorithm/Staging.lean): `card_stagingCells`, `stagingCells_disjoint`, `stagingCells_prefix` |
| Legal simultaneous staging | [`SlidingPuzzle.Algorithm.StagingPath`](SlidingPuzzle/Algorithm/StagingPath.lean): `exists_prefix_disjoint_group_path`, `exists_staging_path` (length at most `1004*k^11`) |
| Staging with last-reservoir representatives | [`SlidingPuzzle.Algorithm.PreparationRepresentatives`](SlidingPuzzle/Algorithm/PreparationRepresentatives.lean): `exists_staging_representative_row_path`, `exists_staging_lastRepresentatives_path` (length at most `1013*k^11`) |
| Blank routing with preservation | [`SlidingPuzzle.Moves.BlankAccess`](SlidingPuzzle/Moves/BlankAccess.lean): `exists_blank_access_path_preserving` |
| Horizontal preparation schedule | [`SlidingPuzzle.Algorithm.PreparationHorizontal`](SlidingPuzzle/Algorithm/PreparationHorizontal.lean): `exists_horizontal_preparation_path`, `exists_horizontal_prepared_path` (combined length at most `1019*k^11`) |
| Protected translations and descending schedule | [`SlidingPuzzle.Moves.ProtectedTranslation`](SlidingPuzzle/Moves/ProtectedTranslation.lean), [`SlidingPuzzle.Moves.RowSchedule`](SlidingPuzzle/Moves/RowSchedule.lean): `exists_protected_row_translation`, `exists_descending_row_schedule` |
| Complete finishing phase | [`SlidingPuzzle.Algorithm.Finish`](SlidingPuzzle/Algorithm/Finish.lean): `Partition.exists_finish_path`, `Algorithm.finishContract : FinishContract 374` |
| Parameterized phase assembly | [`SlidingPuzzle.Algorithm.PhaseAssembly`](SlidingPuzzle/Algorithm/PhaseAssembly.lean): `proposition9_of_transport` requires only `TransportContract` |
| Complete arrangement phase | [`SlidingPuzzle.Algorithm.Arrangement`](SlidingPuzzle/Algorithm/Arrangement.lean): `Partition.exists_arrangement_path`, `Algorithm.arrangeContract_bulk : ArrangeContract 274` |
| Complete transport phase | [`SlidingPuzzle.Algorithm.Transport`](SlidingPuzzle/Algorithm/Transport.lean): `Algorithm.transportContract : TransportContract 82` |
| Reservoir-local transfers | [`SlidingPuzzle.Algorithm.ReservoirSlide`](SlidingPuzzle/Algorithm/ReservoirSlide.lean), [`SlidingPuzzle.Moves.Carry`](SlidingPuzzle/Moves/Carry.lean), [`SlidingPuzzle.Algorithm.TransportCarry`](SlidingPuzzle/Algorithm/TransportCarry.lean): `exists_reservoir_top_path`, `exists_carry`, `exists_transport_exit_count` |
| Unconditional Proposition 9 | [`SlidingPuzzle.Proposition9Complete`](SlidingPuzzle/Proposition9Complete.lean): `average_optimal_length`, `gods_number`, `proposition9` |
| Complete preparation phase | [`SlidingPuzzle.Algorithm.Preparation`](SlidingPuzzle/Algorithm/Preparation.lean): `Partition.exists_preparation_path`, `Algorithm.preparationContract : PreparationContract 1033` |
| Vertical preparation schedule | [`SlidingPuzzle.Algorithm.PreparationVertical`](SlidingPuzzle/Algorithm/PreparationVertical.lean): `exists_vertical_preparation_path` (length at most `14*k^11`, preserving horizontal corridors and representatives) |
| Reachable residual after a solved prefix | [`SlidingPuzzle.Algorithm.ResidualReachability`](SlidingPuzzle/Algorithm/ResidualReachability.lean): `residual_reachable` |
| Residual potential and prefix accounting | [`SlidingPuzzle.Algorithm.ResidualPotential`](SlidingPuzzle/Algorithm/ResidualPotential.lean): `residual_manhattan_eq`, `optimalLength_le_prefix_residual_solution` |
| Complete general-size reduction | [`SlidingPuzzle.Algorithm.GeneralSize`](SlidingPuzzle/Algorithm/GeneralSize.lean): `FourthPowerApproximation`, `uniformApproximation_of_fourthPowerApproximation`, `proposition9_of_fourthPowerApproximation` |
| Four-phase pre/postconditions | [`SlidingPuzzle.Algorithm.PhaseStates`](SlidingPuzzle/Algorithm/PhaseStates.lean): `Prepared`, `Transported`, `Arranged`, `arranged_iff_parity` |
| Count-to-board postcondition | [`SlidingPuzzle.Algorithm.TransportPostcondition`](SlidingPuzzle/Algorithm/TransportPostcondition.lean): `reservoirSorted_iff_boardMatrix_offdiagMass_eq_zero`, `clear_reservoirSorted_blank_in_lastReservoir` |
| Conditional composition of all phases | [`SlidingPuzzle.Algorithm.PhaseContracts`](SlidingPuzzle/Algorithm/PhaseContracts.lean): `FourPhaseContracts.exists_solution`, `fourthPowerApproximation_of_phaseContracts`, `proposition9_of_phaseContracts` |

The required distance estimates and reachability criterion are now proved in
`SlidingPuzzle.Bridge.Statistics` and `SlidingPuzzle.Bridge.Reachability`.
`SlidingPuzzle.Proposition9Reduction.proposition9_of_uniformApproximation`
discharges the statistical assumptions. The general-size reduction and all four
algorithmic phases now instantiate those interfaces without remaining hypotheses.

Protected placement and its arbitrary-target relabeling wrappers compile.
`SlidingPuzzle.Algorithm.BoardTransport.clear_board_count_run_quadratic` proves
count sorting in at most n² transfers for a clear board with the required
last-reservoir representatives. Its margins are derived from exact board counts. `TransportRealization.lean`
and `Transport.lean` now realize that run by legal paths with bounded inefficiency.

## Completed transport and Proposition 9

All four phase contracts are constructed. The current Arrangement contract is
`arrangeContract_bulk : ArrangeContract 274`; the earlier `arrangeContract`
and `phaseContracts` retain their looser constants for compatibility.
`Algorithm.phaseContracts`, `Algorithm.fourthPowerApproximation`, and
`Algorithm.uniformApproximation` have no remaining construction hypotheses.
`Proposition9Complete.lean` applies the existing statistical and general-size
reductions to prove both final results.

`Algorithm/Transport.lean` proves `Algorithm.transportContract : TransportContract 82`.
Each transfer retains the exact vertical and exit inefficiency costs through
composition; rounding entry, vertical, and exit independently would give 83.
The count algorithm takes at most
`k^8` transfers. Its actual endpoint is clear, its reservoirs are sorted, and
its blank is in the last reservoir.

The vertical schedule charges the destination band once. Long slides after that
band decrease the standard Manhattan potential at every step. Short strip jumps
restore all cells except their endpoints; a neighboring tile of the same group
resolves either parity. The temporary filled-blank group invariant proves the
exact count update despite corridor tile permutations.

The constructed Parberry-style solver now proves, for every reachable board
with `n≥4`, an actual legal solution satisfying

```text
2*length ≤ 10*n^3 + 3017*n^2 + 3009*n + 9592.
```

`Parberry.exists_solution_cubic` also gives the simpler integer bound
`length ≤ 5*n^3+1509*n^2+1505*n+4796`. This proves the paper's
`5*n^3+O(n^2)` move-count form unconditionally, with coarser lower-order terms.
Every ordinary placement case, blank normalization, protected first row and
column, residual reachability, and recursive lift is checked. The three boundary
columns use existing concrete routines, and recursion ends at the checked
four-by-four solver. The real-time implementation claim is not formalized.

`Algorithm/ParberryBounds.lean` feeds this construction through the approximation
proof. On finishing blocks of side at least eight it supplies
`CubicSolverBound 227`, down from `527`, and a `447*k^11` finishing path.
Its constructed protected prefix supplies `PrefixPathBound 616`, down from
`1004`, including arbitrary target labels. The resulting unconditional bounds are:

- For side `k^4`, `k≥2`: at most `1088*k^11` inefficient moves and length at most
  `manhattan B+2176*k^11` (`exists_fourth_power_solution_parberry`).
- For every `n≥16`: at most `1899*n^(11/4)` inefficient moves and length at most
  `manhattan B+3798*n^(11/4)` (`exists_solution_with_parberry_uniform`).

Arrangement now follows the paper's shared-staging construction: stage both
families once, exchange their adjacent rows with the checked `θ_m` word, and
reverse the staging. The two sets may reorder internally, including at odd
sizes, while the blank and every outside cell are restored. A pair of size `m`
costs at most `(48*m+4064)*n` for `2*m≤n`, replacing `6044*m*n`.
Both arrangement schedules satisfy the size condition for every `k≥2`.
Their combined length is at most `274*k^11`, down from `3277*k^11`.

The final Proposition 9 proof retains lower-order costs separately. Phase
budgets bound twice the inefficient moves, so half-integer coefficients are
exact. The leading inefficiency coefficients are now `11.5` for Preparation,
`9` for Transport, and `14.5` for the halved arrangement-and-finish suffix;
size reduction adds `60`.

- Transport: each transfer may permute tiles inside a reservoir. The blank first
  slides to the top of its reservoir, making the entry jump short. At the exit
  it walks to the source tile and carries it to the corridor side with
  five-move carries (`Moves/Carry.lean`, `Algorithm/TransportCarry.lean`).
- Staging: the quotas lie in the first `k³` columns or first `k²` rows, so a
  column-only prefix (`Algorithm/Parberry/MixedPrefix.lean`,
  `Algorithm/MixedStaging.lean`) replaces `k³` complete layers: `7.5` instead
  of `15`.
- Vertical spreading: each column is translated in only as many chunks as its
  own distance requires (`exists_descending_column_schedule_var`): `4` instead
  of `8`.

The checked legal solution bounds are:

```text
n = k^4:  2*inefficiency ≤ 70*k^11 + 19030*k^10
n ≥ 16:   inefficiency ≤ 95*n^(11/4) + 21527*n^(5/2)
          length ≤ Manhattan + 190*n^(11/4) + 43054*n^(5/2)
```

Thus the arbitrary-size leading inefficiency coefficient falls from `1648.5`
to `149.5` and then `95`. The eventual adapter gives inefficiency `95.5` and
additive length `191`, at the explicit unoptimized threshold `max 16 (43054^4)`.
The older `3127`/`6254` fourth-power
and `7143`/`14286` arbitrary-size theorems remain available.

The stronger exact bound `5*n^3`, without a quadratic remainder, remains
conditional on `Parberry.LayerPathBound`. That contract requires
`length+15*n ≤ 15*n^2+5` for the outer layer and would also imply
`PrefixPathBound 15`. The constructed layer instead proves
`length ≤ 15*n^2+3002*n+1`. The projected `3874` additive and `1937`
inefficiency coefficients therefore remain conditional; they are not claimed
from the newly proved asymptotic solver.

See [phase contracts](PHASE_CONTRACTS.md), [status](STATUS.md), and
[proof notes](PROOF_NOTES.md) for interfaces and proof-to-paper details.
Reused concrete lemmas are recorded under `ThirdParty/Zhong`; old phase
assumptions and diagnoses are excluded.

Run `lake build` and `lake env lean Checks/Axioms.lean` to check the project and
inspect the axioms of its constructions and both unconditional final theorems.
