## Cheaper staging and vertical spreading (2026-09-24)

Phase budgets (`CostedPhase` in `Algorithm/LeadingBudgets.lean`) now bound twice
the inefficient moves, so half-integer leading coefficients are exact.

- `Algorithm/Parberry/MixedPrefix.lean`: `exists_mixed_prefix` solves the first
  `d` columns and first `r` rows toward an arbitrary target with the standard
  blank, at doubled cost `(d+r)*(15*n^2+3002*n+1)`. Columns use the transposed
  row solver (`exists_columns_prefix`), and rows use the rectangular row solver
  right of the solved columns (`exists_right_rows`).
- `Algorithm/MixedStaging.lean`: `representativeStaging_mixed` fills the staging
  quotas and representatives with `r=k^2+1`, `d=k^3`. Staging drops from `15` to
  `7.5`.
- `CostedConstruction.lean`: the staging chain takes any `RepresentativeStaging`
  provider; `representativeStaging_of_cost` keeps the old prefix route.
- `Moves/ColumnSchedule.lean`: `exists_descending_column_schedule_var` allows a
  chunk count per column. Column `i` needs `i/k^2` chunks, and `sum_div_sq_le`
  bounds the total by `k^3(k-1)/2`. Each band costs `2*length ≤ 8*k^10`, so
  vertical spreading drops from `8` to `4`.

Leading inefficiency is now size reduction `60` + Preparation `11.5` + suffix
`14.5` + Transport `9` = `95`. Fourth powers: `2*inefficiency ≤ 70*k^11+19030*k^10`.
For every `n≥16`: inefficiency `≤ 95*n^(11/4)+21527*n^(5/2)` and length
`≤ Manhattan+190*n^(11/4)+43054*n^(5/2)`. The eventual coefficients are `95.5`
and `191`, at threshold `max 16 (43054^4)`.

Validation: full build passes (8852 jobs); the axiom audit passes with only
standard Lean axioms and no `sorry`.

## Cheaper transport transfers (2026-09-24)

`TransportStepBound` only constrains clear corridors, the blank's reservoir, and
reservoir counts, so a transfer may permute tiles inside a reservoir. Transport
now uses this at both ends:

- `Algorithm/ReservoirSlide.lean`: `exists_reservoir_top_path` slides the blank to
  the first row of its reservoir; `boardMatrix_swap_same_reservoir` proves counts
  are unchanged. The entry jump then crosses at most `k+1` rows.
- `Moves/Carry.lean`: `exists_row_walk` and `exists_carry` (five moves per cell).
- `Algorithm/TransportCarry.lean`: `exists_transport_carry_exit` enters the source
  reservoir by a short jump, walks to the selected tile, carries it to the
  corridor side, and exchanges it into the corridor by two short jumps and one
  corridor move. `exists_transport_exit_count` falls back to the direct jump
  when the tile is already within two columns of the corridors.
- `Path.two_inefficientMoves_le_of_blank_swap` charges restoring jumps at half
  their length.

The transfer bound is `8*k^3+E+69*k^2+13*k+189` (was `51*k^3+E+1`), and the
Transport leading coefficient is `9` (was `52`). The jump-only construction is
kept as `transportStepBound_of_vertical_bound_jump` (`27*k^3+E+1`), which still
supplies the legacy `TransportContract 82`.

Fourth powers: `2*inefficiency ≤ 93*k^11+24402*k^10` (was `179*k^11+24230*k^10`).
For every `n≥16`: inefficiency `≤ 106.5*n^(11/4)+24213*n^(5/2)` (was `149.5`); the
eventual coefficients are `107` for inefficiency and `214` for additive length
(were `150`/`300`), at threshold `max 16 (48426^4)`.

Validation: full build passes (8850 jobs); the axiom audit passes with only
standard Lean axioms and no `sorry`.

## Shared-staging arrangement (2026-09-24)

Arrangement now implements the paper's access / `θ_m` / reverse-access set
exchange. The legal-path budget is `274*k^11`, down from `3277*k^11`; the
separate leading budget is `24*k^11+786*k^10`, down from
`3022*k^11+3022*k^10`. The blank and every outside cell are restored, and odd
set sizes and the full-row staging case `k=2` are covered.

The final Proposition 9 interface uses the improved construction. Its explicit
arbitrary-size bound is `149.5*n^(11/4)+24127*n^(5/2)` inefficient moves for
`n≥16`; the eventual leading coefficient is `150`. The all-size uniform
Parberry bound improves from `3400` to `1899`. Legacy coarse contracts remain
available. See the final section of `PROOF_NOTES.md` for the construction.

Validation: full build passes (8847 jobs); the expanded axiom audit passes
(367 declarations, only standard Lean axioms).

# Formalization status

Updated 2026-09-24. **Proposition 9 is proved unconditionally.**
`SlidingPuzzle.average_optimal_length` and `SlidingPuzzle.gods_number` prove the
two required `O(n^(11/4))` errors, and `SlidingPuzzle.proposition9` combines them.
They concern the uniform reachable orbit of the fixed standard target.

Leading-term accounting now keeps lower-order work separate throughout all four
phases. `LeadingBudget` stores `A*k^11+B*k^10`; composition adds both fields
separately. The new cost-function prefix and solver interfaces preserve the
polynomial costs through allocation, borrowing, parity repair, and scheduling.

| Phase | Leading coefficient | Remainder coefficient (k^10) | Quantity |
| --- | ---: | ---: | --- |
| Preparation | 11.5 | 350 | Inefficiency |
| Transport | 9 | 190 | Inefficiency |
| Arrangement | 3022 | 3022 | Length |
| Finish | 5 | 17164 | Length |

Halving the complete solving suffix gives fourth-power inefficiency
`(3177/2)*k^11+13233*k^10`. Arbitrary-size reduction adds leading coefficient
60. `Algorithm.exists_solution_with_leading_bound` proves, for every `n≥16`,

```text
inefficiency ≤ (3297/2)*n^(11/4) + 25245*n^(5/2),
length ≤ Manhattan + 3297*n^(11/4) + 50490*n^(5/2).
```

Only at the final asymptotic step is the remainder absorbed. The eventual
bounds are inefficiency `1649*n^(11/4)` and additive length `3298*n^(11/4)`.
The explicit sufficient threshold `max 16 (50490^4)` is intentionally loose.
`Proposition9Complete.lean` now uses `Algorithm.uniformApproximation_leading`;
Proposition 9's statement is unchanged. Existing all-size uniform bounds remain
available. The following paragraphs describe those earlier uniform interfaces.

The Parberry-style `5*n³+O(n²)` solver is now **constructed and proved**.
`Parberry.exists_solution_cubic_aux` gives, for every reachable board with `n≥4`,

```text
2*length ≤ 10*n³ + 3017*n² + 3009*n + 9592.
```

`Parberry.exists_solution_cubic` gives the integer-coefficient version
`length ≤ 5*n³+1509*n²+1505*n+4796`. No unproved layer or finishing input remains
in these theorems. The construction checks all ordinary placement cases,
normalizes the blank, solves a complete row, lifts a rectangular row solver to
the protected first column, and recurses with verified residual reachability.
Inactive moves are deleted before rectangular lifting so they cannot cross the
removed row. The four-by-four base uses the existing concrete solver.

The ordinary placement allowance is
`length+2*min j (n-j)+7 ≤ 8*n`. The complete row satisfies
`2*length ≤ 15*n²+3002*n+1`; the complete layer satisfies
`length ≤ 15*n²+3002*n+1`. The larger linear remainder pays for three boundary
columns using existing checked routines. It changes the quadratic remainder of
the full solver, not its leading cubic coefficient. The paper's real-time
implementation claim is not part of this formalization.

The same construction improves both solver and prefix interfaces:
`Parberry.cubicSolverBound : CubicSolverBound 227` for sides at least eight, and
`Parberry.prefixPathBound : PrefixPathBound 616`. The prefix also retains the
more informative bound `(15*n²+3002*n+1)*d` before uniform rounding.
`Algorithm/ParberryBounds.lean` proves the resulting unconditional bounds:

- Side `k^4`, `k≥2`: inefficiency `2589*k^11`, additive length `5178*k^11`.
- Every `n≥16`, retaining the size-reduction remainder: inefficiency
  `2649*n^(11/4) + 12008*n^(7/4) + 4*n^(3/4)`; additive length is twice this.
- Every `n≥16`, a uniform bound: inefficiency `3400*n^(11/4)`, additive length
  `6800*n^(11/4)`. The older `5053` and `10106` bounds remain available.

Preparation costs `645`, transport `82`, and arrangement plus Finish have
inefficiency `(3277+447)/2=1862`. Keeping the prefix polynomial separate,
size reduction contributes only `60*n^(11/4)+12008*n^(7/4)+4*n^(3/4)` to
inefficiency, giving leading coefficient `645+82+1862+60=2649`. The width
estimate `n-k^4 ≤ 4*n^(3/4)` avoids rounding the ambient side up to `(k+1)^4`.
Alternatively, absorbing the remainder at `n≥16` gives a uniform prefix
coefficient `811` and total `2589+811=3400`. Earlier bounds remain available
under their existing names. The older
phase package `⟨1033,82,3277,374⟩` also remains available. Proposition 9 and all
four phase constructions continue to be unconditional.

The exact `5*n³` solver and `15*d*n²` prefix remain stronger conditional
results. The constructed layer does not satisfy `Parberry.LayerPathBound`'s
sharper linear term. Accordingly, the projected arbitrary-size additive bound
`3874*n^(11/4)` and inefficiency bound `1937*n^(11/4)` are still conditional.
Earlier dated checkpoints below record historical progress.

Validation: the full build succeeds (8844 jobs); `Checks/Axioms.lean` audits
356 declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
The new construction contains no proof placeholders or custom axioms.

User constraint: this workspace was intentionally started afresh. Reuse only
concrete checked lemmas after proving compatibility with this model. Do not
inherit the neighboring project's diagnosis that a routine construction is
impossible, or its unfinished Phase I availability/schedule assumptions. The
old phase modules and notes are excluded; see `ThirdParty/Zhong/NOTICE.md`.

## Reproducible environment

- Lean: `leanprover/lean4:v4.33.1`.
- mathlib: tag `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- All transitive revisions are pinned in `lake-manifest.json`.
- This workspace reuses existing matching dependency checkouts through ignored
  `.lake/packages` symlinks. A fresh checkout can fetch the pinned dependencies
  and caches with `lake exe cache get`, then run `lake build`.
- `SlidingPuzzle.lean` is the umbrella module: the default build checks all
  integrated proof modules. `lake env lean Checks/Axioms.lean` audits key exports.

## Package ownership, status, and checks

| Package | Owner | Status | Validation | Outstanding obligations |
| --- | --- | --- | --- | --- |
| A: boards and paths | integration | Complete; API frozen | `lake build SlidingPuzzle.Paths SlidingPuzzle.Target` | None for these core definitions |
| A/B: finite statistics | statistics agent, integrated | Complete | `lake build SlidingPuzzle.Statistics` | None for finite generic transfers |
| B: potential | manhattan agent, integrated | Complete | `lake build SlidingPuzzle.Manhattan` | None for exact identity and lower bound |
| C: universal distance upper bound | manhattan agent, integrated | Complete | `lake build SlidingPuzzle.DistanceEstimates SlidingPuzzle.StatisticalBounds` | Orbit mean and reachable lower bound are separate |
| C: orbit parity and remaining estimates | integration, checked source reuse | Complete for the required estimates | `lake build SlidingPuzzle.Bridge.Reachability SlidingPuzzle.Bridge.Statistics` | Exact mean identity is optional and not claimed |
| D: local moves | integration / smaller-model agents | Local cycles, cubic solver and protected row/column paths complete | `lake build SlidingPuzzle.Moves.Placement` | Phase-specific embedded operations |
| E: fourth-power algorithm | integration | All four phases complete (`1033`, `82`, `3277`, `374`) | `lake build SlidingPuzzle.Algorithm.PhaseAssembly` | None |
| F: general dimensions | integration | Complete and instantiated by `Algorithm.uniformApproximation` | `lake build SlidingPuzzle.Algorithm.PhaseAssembly` | None |
| G: final assembly | integration | Both unconditional theorems and `proposition9` complete | `lake build SlidingPuzzle.Proposition9Complete` | None |
| Paper audit | paper_audit agent | Complete for foundation/statistics claims | Reproducible diagnostics in `PROOF_NOTES.md` | Algorithm details still require proof-level audit |
| Documentation | integration / smaller-model reviewer | Current | `README.md`, this file, `PROOF_NOTES.md` | Update as each missing dependency closes |

## Frozen core interface

Names are in namespace `SlidingPuzzle` unless qualified further.

- `Cell n := Fin n × Fin n`; `Tile n := Fin (n*n)`; `Board n := Cell n ≃ Tile n`.
- `target n : Board n` is `finProdFinEquiv.trans (finRotate (n*n))`.
  `target_apply_val` proves the row-major numeric formula;
  `target_bottomRight` proves the corner holds zero.
- `position B t`, `blank B`, `gridDistance a b : ℕ`, `swapCells B a b`.
- `Step B C` swaps the blank with a cell at grid distance one; `Step.symm`.
- Blank/move/path/orbit interfaces require `[NeZero n]`. Valid sizes `n ≥ 2`
  are included; the four all-dimension real statistics equal zero below 2.
- `Path A B : Type`, constructors `Path.nil`, `Path.cons`; `Path.length : ℕ`,
  `Path.append`, `Path.reverse`; `Path.length_append`, `Path.length_reverse`.
- `Reachable B := Nonempty (Path (target n) B)`; `ReachableBoard n` is its
  subtype, with `Fintype` and `Nonempty` instances and `targetBoard n`.
- `exists_solution B : Nonempty (Path B.val (target n))`.
- `optimalLength B : ℕ` is the least solution length, defined with `Nat.find`.
- `shortest_witness B : ∃ p : Path B.val (target n), p.length = optimalLength B`.
- `optimalLength_le_path_length B p : optimalLength B ≤ p.length`.
- `optimalLength_target n : optimalLength (targetBoard n) = 0`.
- `manhattan B : ℕ` sums distances of nonzero labels;
  `manhattan_target n : manhattan (target n) = 0`.

## Proved downstream interfaces

### Potential and statistics

- `Step.manhattan_delta`: `manhattan B + 1 = manhattan C ∨ manhattan C + 1 = manhattan B`.
  Integer and real signed variants: `Step.manhattan_delta_int`, `_real`.
- `Path.inefficientMoves` counts increasing steps.
- `Path.length_add_manhattan p`:
  `p.length + manhattan B = manhattan A + 2 * p.inefficientMoves`.
- `Path.solution_length p` for a solution:
  `p.length = manhattan A + 2 * p.inefficientMoves`.
- `manhattan_le_optimalLength B` is unconditional for each reachable board.
- `finiteMean`, `finiteMaximum`, with `*_mono`, `*_add_const`, `*_sandwich`,
  and `finiteMaximum_attained`.
- Orbit statistics: `orbitAverageOptimalLength`, `orbitAverageManhattan`,
  `orbitMaximumManhattan`, `orbitGodsNumber`.
- Extended sequences `ℕ → ℝ`: `averageOptimalLength`, `averageManhattan`,
  `maximumManhattan`, `godsNumber`, with `*_of_two_le`, `*_of_lt_two`.
- `statistics_sandwich n hn hlo hhi` transfers a board-independent additive
  error to both means and maxima. `hlo` is supplied by the proved potential bound.
- `midpointDeviation_exact n`: `4 * midpointDeviation n + n % 2 = n*n`.
- `manhattan_le_cube B : manhattan B ≤ n^3`; `manhattan_le_cube_real` is its cast.
- `maximumManhattan_le_cube n : maximumManhattan n ≤ (n : ℝ)^3` for every n.
- `averageManhattan_le_averageOptimalLength`, `maximumManhattan_le_godsNumber`.
- `maximumManhattan_abs_error_le` reduces the maximum error to just a lower bound.

### Necessary orbit parity

- `boardSign B` is the sign of the permutation relative to the target.
- `colorSign c := (-1 : ℤˣ)^(c.1.val + c.2.val)`.
- `Step.parityInvariant` and `Path.parityInvariant` prove preservation of
  `boardSign B * colorSign (blank B)`.
- `reachable_boardSign_mul_colorSign` proves the target parity condition for
  every reachable board. `reachable_iff_parityInvariant` in the bridge proves the converse for n≥2.

### Finite local and algorithm accounting

- `Step.toPath`, `movePath`, and their exact length-one theorems.
- `Executes B cs C` records legal blank destinations.
- `Executes.exists_path`: an executable word has a path of length `cs.length`.
- `Executes.preserves`: a cell outside the initial blank and word destinations
  retains its tile; `Executes.append` concatenates words.
- `reachableAfter` and `optimalLength_le_word_then_solution` preserve the orbit
  and convert a word followed by a solution into an OPT upper bound.
- `cycleBoard`, `executes_cycle`, `exists_path_cycle` give an actual four-move
  cycle, with `blank_cycle`, `cycle_preserves`, and the exact tile rotation
  `cycle_rotate` under distinct-vertex hypotheses.
- `Path.inefficientMoves_append`, `Path.inefficientMoves_le_length`.
- `Path.manhattan_end_le`, `Path.prefix_solution_bound`,
  `optimalLength_le_prefix_solution`: the prefix overhead is at most twice its length.
- `Path.four_phase_solution_bound` combines **given** legal phase paths and
  inefficient-move bounds. It neither constructs phases nor proves their bounds.

### Dimension arithmetic and asymptotics

- `fourthRoot n := Nat.sqrt (Nat.sqrt n)`; `le_fourthRoot_iff`.
- `exists_fourth_power_dimension hn` for `16 ≤ n`: a k with `2 ≤ k`,
  `k^4 ≤ n < (k+1)^4`, and `n-k^4 ≤ 15*k^3`.
- `outer_layer_budget_le`: `(n-k^4)*n^2 ≤ 3840*k^11` when `1 ≤ k` and `n<(k+1)^4`.
- `nat_sq_le_rpow_eleven_fourths`, `nat_sq_isBigO_rpow_eleven_fourths`,
  `error_isBigO_rpow_eleven_fourths`, `sandwich_isBigO_rpow_eleven_fourths`.
- `fourth_power_gap_le`, `pow_eleven_le_rpow_of_fourth_power_le`.

## Exact remaining assembly contract

`UniformApproximation` in `Proposition9.lean` is the following **unproved proposition**:

```text
∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ hn : 2 ≤ n,
  letI : NeZero n := ⟨by omega⟩
  ∀ B : ReachableBoard n,
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)
      + C * Real.rpow (n : ℝ) (11 / 4 : ℝ)
```

`conditional_average_optimal_length` additionally assumes
`∃ C ≥ 0, ∀ᶠ n in atTop, |averageManhattan n - (2/3)*n^3| ≤ C*n^2`.
`conditional_gods_number` additionally assumes
`∃ C ≥ 0, ∀ᶠ n in atTop, |maximumManhattan n - n^3| ≤ C*n^2`.
`conditional_proposition9` combines them. None asserts an unconditional theorem.

## Next work, in dependency order

1. Continue tightening the remaining transport and arrangement constants if
   desired; all four concrete contracts are already proved.
2. Keep the documentation synchronized with any subsequent bound changes.
3. Re-run `lake build` and `lake env lean Checks/Axioms.lean` after changes.

No critical dependency is represented by a custom axiom or an unfinished proof.
The missing dependencies remain explicit open work and conditional hypotheses.

## Latest integrated validation (2026-09-20)

- `lake build`: successful (8803 jobs), including complete preparation,
  arrangement, finish, and the reduction to Transport alone.
  Upstream and a few local style warnings remain; no proof errors.
- `lake env lean Checks/Axioms.lean`: successful; 168 checked declarations report
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Source scan found no proof placeholders or custom axiom declarations.
- This audits the current concrete interfaces and conditional final reduction;
  it is not a proof of unconditional Proposition 9.

Delegation preference: use smaller models for routine documentation, checks,
and bounded proof work where sufficient. The final documentation pass used
Luna; the four-cycle and necessary-parity proofs used Terra.

## New checked bridge exports (current continuation)

- `Bridge/Words.lean`: `path_of_zhong_word` drops invalid identity operations,
  returning a legal path no longer than the word; `zhong_word_of_path` gives
  an equally long word; `zhong_reachable_iff_path`, `reachable_iff_zhong` identify
  the reachable sets. No unproved reachability identification is used.
- `Bridge/Distance.lean`: `manhattan_eq_zhong_D` proves the blank-excluding sum
  is exactly the imported potential.
- `Bridge/Reachability.lean`: `reachable_iff_parityInvariant` proves both
  directions for `2 ≤ n`, using the general grid proof and checked 2×2 table.
- `Bridge/Statistics.lean`: `orbitAverageManhattan_eq_zhong_avgD` identifies the
  real finite mean with the rational mean over exactly the same orbit.
  `averageManhattan_error_bound` (n≥2) and `maximumManhattan_error_bound` (n≥3)
  have explicit error `3*n²`; their `_eventually` theorems discharge package C.
- `Moves/Placement.lean`: `exists_solution_cubic` and `optimalLength_le_cubic`
  have bound `2000*n³` for n≥4; `exists_protected_row_path` and
  `exists_protected_column_path` preserve the prescribed solved cells.
- `Proposition9Reduction.lean`: `proposition9_of_uniformApproximation` proves
  both desired concrete asymptotic conclusions assuming only UniformApproximation.
- `Algorithm/TransportCounts.lean`: `exists_sorted_run` constructs the min-source
  count algorithm under explicit capacity-margin and initial-last-row invariants,
  with iterations ≤ initial off-diagonal mass and final off-diagonal mass zero.
  This is a count algorithm, not yet a legal board-level transport implementation.

The reused source snapshot has compiled, preserving its original source text and
license headers; inherited style warnings are recorded in build logs. Its phase
modules are excluded. SHA-256 source hashes and licensing provenance are under
`ThirdParty/Zhong`. Current axiom checks on the connected statistics, sufficiency,
solver, and reduction results report only standard Lean logical axioms.

## Board/count connection (2026-09-13 continuation)

- `Algorithm/Partition.lean`: exact cover and disjointness/uniqueness of regions
  and target groups, with the blank excluded explicitly.
- `Algorithm/Cardinalities.lean`: H size n, V size k³−k, reservoir size
  (k³−k)(k³−k²), square size k⁶. `card_targetGroup` accounts for the blank;
  `square_target_blank` identifies the unique last group.
- `Algorithm/BoardCounts.lean`: `sum_regions`, `clear_corridor_count`,
  `reservoirCount_row`, and `reservoirCount_column` derive the exact margins
  from an actual board, rather than assuming them for an arbitrary matrix.
- `Algorithm/BoardTransport.lean`: `boardMatrix_margins`,
  `clear_board_has_sorted_count_run`, `boardMatrix_mass_le`, and
  `clear_board_count_run_quadratic` connect prepared boards to count sorting.
  The representative hypothesis is explicit; no board path is claimed here.
- `Moves/Relabel.lean`: blank-fixing relabeling preserves legal paths and length;
  arbitrary-target protected row/column paths compile.

The smaller-model agent hit its usage limit during the relabeling extension.
Integration completed and checked that draft locally; no usage reset was used.

- `Moves/Strips.lean`: `exists_blank_access_path` reaches any blank destination
  within its grid distance; four horizontal/vertical strip swap families have
  explicit length bounds `20*l+1` or `24*l+1` and exact transposition endpoints.
- `Algorithm/CountSwap.lean`: `reservoirCount_transport_swap` verifies the exact
  incoming-tile update, and `clear_swap_reservoirs` preserves Clear.
- `boardMatrix_choice_endpoint` supplies an actual source tile for each count
  choice and verifies its endpoint matrix update. It deliberately does not claim
  that an arbitrary endpoint transposition has a legal path. The strip lemmas
  provide specific legal cases; general transfer routing remains open.

## Final checkpoint before pausing (2026-09-13)

User requested stopping for now. All source files listed below are integrated.

- `Moves/Prefix.lean`: `exists_prefix_path` constructs a legal path placing the
  first d rows and columns against an arbitrary target with standard blank,
  within `1004*d*n²` moves, when d+4≤n. `exists_fourth_power_prefix` gives
  `3855360*k¹¹` for the general-size outer prefix.
- `Algorithm/Allocation.lean`: an injective nonblank partial assignment extends
  to a full target board; group cardinality bounds produce such an assignment.
  `exists_prefix_group_path` combines allocation and the quantitative prefix
  path. No availability assumption about nearby tiles is used.
- `Algorithm/PreparationCapacity.lean`: sufficient labels for every corridor
  quota, one spare per non-last group, and reservoir capacity at least k².
- `Algorithm/Staging.lean`: the paper's initial A/B/C staging regions are defined;
  their individual cardinalities and the combined compressed-column cardinality
  are proved. **The full staging union's quota, cross-group disjointness, and
  prefix-containment interface still need integration/proofs.**
- `Moves/Translation.lean`: actual row and column-block translation paths with
  explicit length bounds and stated preservation regions. Blank access and the
  complete descending schedule remain separate.
- `Moves/Embedding.lean`: a local path lifts into an embedded board with exactly
  the same length and fixes outside cells.
- `Algorithm/Residual.lean`: constructs the relabeled residual board after a
  solved prefix; any solution of that residual lifts without extra moves.
  **Residual reachability and potential comparison are not yet proved.**

Immediate continuation: finish the staging-region quota/disjointness and feed
it into `exists_prefix_group_path`; handle last-reservoir representatives, then
assemble the translation schedule. The main uniform approximation is still open.
The staging agent hit its usage limit while drafting its final lemmas; integration
repaired and compiled that draft. No unfinished `.lean` proofs were retained.

## Current continuation (2026-09-19)

This checkpoint supersedes the open staging and residual items in the earlier
pause checkpoint. Terra handled staging combinatorics and residual parity;
Luna handled the staging allocation path. Integration proved the potential
comparison and general-size reduction and reviewed the combined interfaces.

- `Algorithm/Staging.lean`: `card_stagingCells` gives exactly
  `n+k²*(k³-k)` cells per group; `stagingCells_destination_unique`,
  `stagingCells_disjoint`, `stagingCells_pairwise_disjoint`, and
  `stagingCells_prefix` discharge the missing combinatorial interfaces.
- `Algorithm/StagingPath.lean`: `exists_prefix_disjoint_group_path` fills any
  disjoint family of prefix quotas within `1004*d*n²`; `exists_staging_path`
  instantiates all A/B/C quotas with a legal path of length at most `1004*k¹¹`.
  No local-availability or reachability assumption on the initial board is used.
- `Algorithm/ResidualReachability.lean`: `residual_reachable` proves local
  reachability for residual side length at least two from global reachability
  and a solved prefix. Permutation sign and checkerboard color are preserved.
- `Algorithm/ResidualPotential.lean`: `residual_manhattan_eq` identifies residual
  potential exactly; `optimalLength_le_prefix_residual_solution` retains the
  factor-two prefix overhead when lifting a residual approximation.
- `Algorithm/GeneralSize.lean`: `optimalLength_le_of_fourth_power_bound` gives
  `D+(K+7710720)*k¹¹` for the ambient puzzle, assuming `D+K*k¹¹` on the residual.
  `uniformApproximation_of_fourthPowerApproximation` proves the all-dimension
  interface for `n≥16`; `proposition9_of_fourthPowerApproximation` supplies both
  asymptotic conclusions from that single remaining algorithmic hypothesis.

`FourthPowerApproximation` means `∃ K : ℕ, ∀ k≥2, ∀ A : ReachableBoard (k^4),
optimalLength A ≤ manhattan A.val + K*k^11`, with the nonzero dimension instance
supplied internally. It is **not proved**. The four phase paths and their
inefficiency bounds must supply it; a new conditional reduction is not a proof
of Proposition 9.

Next constructive work: realize count transport with bounded inefficiency and
construct Arrange/Finish. Preparation, including both corridor families and
representatives, is now complete.
General-size reachability and potential comparison are no longer open work.

## Frozen phase handoff (2026-09-20)

- `Algorithm/PhaseStates.lean` defines `LastRepresentatives`, `SquaresSorted`,
  and the endpoint states `Prepared`, `Transported`, and `Arranged`. Each state
  carries global reachability. Preparation and transport retain `Clear`;
  arrangement retains square membership instead. Blank location is explicit.
  `squaresSorted_iff_positions` also proves the equivalent label-based statement:
  every target-group label is actually located in its corresponding square.
- `arranged_iff_parity` identifies the Finish input's reachability field with
  the global target parity invariant. No field asserts internal reachability
  of every square. Finish must construct and budget local repairs and access.
- `Algorithm/TransportPostcondition.lean` proves that sorted reservoirs are
  equivalent to zero off-diagonal mass of the board's own count matrix. A clear
  board with sorted reservoirs necessarily has its blank in the last reservoir.
- `Prepared.of_path`, `Transported.of_path`, and `Arranged.of_path` derive
  endpoint reachability from the actual path. `Transported.of_count_endpoint`
  requires both a path and a sorted matrix belonging to its concrete endpoint;
  it does not turn an abstract count run into a legal path.
- `Algorithm/PhaseContracts.lean` defines `PreparationContract`,
  `TransportContract`, `ArrangeContract`, and `FinishContract` for all `k≥2`.
  `PhaseBudgets` chooses constants independently of dimension and input board;
  each contract supplies a legal path with inefficient moves at most `C*k^11`.
- `FourPhaseContracts.exists_solution` proves that the four endpoints compose
  into a legal solution with additive bound `2*(C₁+C₂+C₃+C₄)*k^11`.
  `fourthPowerApproximation_of_phaseContracts`,
  `uniformApproximation_of_phaseContracts`, and `proposition9_of_phaseContracts`
  connect these obligations to the existing reductions. They explicitly assume
  `FourPhaseContracts`; no instance has been constructed.

Owners: Terra proved the state predicates and count postcondition bridge;
integration defined the uniform contracts and composition; Luna reviewed the
handoffs, parity responsibility, and absence of hidden count-to-path assumptions.
The exact implementation handoff is in `PHASE_CONTRACTS.md`. Phase constructors
are the next work, not new stronger assumptions at a later boundary.

## Preparation representatives (2026-09-20)

Preparation was selected as the most accessible phase because allocation,
staging, and row translation were already proved. A concrete missing subphase
is now constructed in `Algorithm/PreparationRepresentatives.lean`:

- `exists_representative_staging_path` fills the A/B/C quotas and one extra
  source cell for each nonfinal group within `1004*k¹¹` moves. The extra cells
  are `(k², k⁴-k²+i)`; the existing group capacities prove their availability.
- `exists_staging_representative_row_path` routes the blank through the unused
  rectangle and translates the spare row to `(k⁴-3, k⁴-k²+i)`. It preserves
  every original staging quota, retains explicit representative positions,
  and bounds the whole path by `1013*k¹¹` moves for every input board.
- `representative_destination_in_last_reservoir` checks the destination geometry,
  including `k=2`. `exists_staging_lastRepresentatives_path` derives the exact
  `LastRepresentatives` count condition from those tiles.
- `Moves/BlankAccess.lean` adds `exists_blank_access_path_preserving`: access
  changes only cells in the rectangle spanned by the initial and final blank.
- The allocation and disjoint-quota paths now also have `_with_blank` variants,
  proving that the blank is outside the solved prefix. Existing interfaces are
  retained as wrappers.

The access segment costs at most `2*k⁴`, and the representative translation at
most `7*k⁶`. Both preserve staging because staging cells satisfy row `< k²`
or column `< k³`. This construction requires no reachability, local availability,
or abstract path hypothesis. Reachable inputs retain reachability via the path.

**Still open:** assemble the horizontal and vertical translations to `Clear`
and prove that they preserve the representative row. This result is a completed
preparation subphase, not an inhabitant of `PreparationContract`. The four-phase
approximation and unconditional Proposition 9 remain unproved.

Validation for this continuation: `lake build` succeeds (8776 jobs), and
`lake env lean Checks/Axioms.lean` succeeds for 97 declarations using only
`propext`, `Classical.choice`, and `Quot.sound`. The source scan found no proof
placeholders or custom axiom declarations; the word “admit” occurs only as an
ordinary verb in an existing staging-path documentation comment.

## Horizontal preparation schedule (2026-09-20 continuation)

Preparation step (ii) is now fully constructed, including blank access and
preservation. `Algorithm/PreparationHorizontal.lean` exports:

- `exists_horizontal_preparation_path`: from the staged board with the blank
  on the final row, fill every horizontal corridor within `12*k¹⁰` moves.
  Every compressed vertical-quota cell and every explicit representative cell
  retains its original label. The blank returns to its starting cell.
- `exists_horizontal_prepared_path`: from any input board, compose staging,
  representatives, and the horizontal schedule within `1025*k¹¹` moves. Its
  endpoint has every horizontal corridor in its required group, all compressed
  vertical quotas still filled, all nonfinal representatives at their designated
  last-reservoir positions, and the blank on the last row.

The proof uses the concrete one-row shift from Lemma 1 and explicitly undoes
blank access. `Path.exists_conjugated` constructs the return path by blank-fixing
relabeling: if access fixes the local operation's support and the local operation
returns its blank, the conjugated path retains the local effect and restores
all outside cells. `exists_protected_row_shift` applies this to the two data
rows of the shift word. `exists_protected_row_translation` iterates those shifts,
and `exists_descending_row_schedule` processes sources from the bottom upward.
The destination rows are proved strictly increasing, so completed destinations
and unprocessed sources survive each iteration.

The previous row-translation and representative APIs remain available. Their
new `_with_blank` variants additionally expose the exact blank endpoint needed
for composition; no new input assumption is imposed on the initial board.

**Next:** build the vertical block schedule (paper step (iii)), preserving the
completed horizontal corridors and representative row, then instantiate
`PreparationContract`. Its cost still needs the `O(k¹¹)` bound: blindly using
the new unit-shift construction for every vertical column only gives a crude
`O(k¹²)` estimate. The existing block-column translation is available for the
sharper construction, with its scratch-row preservation obligation explicit.
No preparation contract or unconditional Proposition 9 is claimed yet.

Validation: `lake build` succeeds (8780 jobs), and
`lake env lean Checks/Axioms.lean` audits 107 declarations with only the standard
Lean axioms. The source scan found no proof placeholders or custom axioms.
The preparation paragraph and Lemma 1 were also checked against printed page 140
of the local paper; all imported source files remain unchanged.

## Preparation phase complete (2026-09-20 continuation)

This checkpoint supersedes the open vertical-schedule and preparation-contract
items above. `Algorithm/Preparation.lean` now proves:

- `Partition.exists_preparation_path`: for every `k≥2` and **every** board of
  side `k⁴`, construct a legal path of length at most `1039*k¹¹` whose endpoint
  satisfies `Clear` and `LastRepresentatives`. It has no reachability or local
  availability assumption.
- `Algorithm.preparationContract : PreparationContract 1039`: reachable inputs
  produce the original `Prepared` state, including reachability, within the
  required uniform inefficient-move bound. No contract was strengthened or
  weakened to accommodate the implementation.

The vertical proof in `Algorithm/PreparationVertical.lean` processes each row
band independently and its compressed columns in descending destination order.
`exists_vertical_preparation_path` costs at most `14*k¹¹` moves and preserves
all horizontal corridors and each representative cell. The exact blank column
from horizontal preparation is carried through a `_with_blank` variant; the
previous interface remains as a wrapper.

`Moves/ColumnTranslation.lean` divides each column translation into at most `k`
chunks, each of width at most `k³`. Nearby access costs at most
`t*(2*t+6*H+8)` inside a chunk, with at most `4*n` additional moves to reach
and restore its access route. This gives at most `14*k⁷` moves per column,
`14*k¹⁰` per row band, and `14*k¹¹` over all bands. The paths restore all cells
outside their data rectangles and return the blank to its starting cell.
`Moves/ColumnSchedule.lean` proves the descending composition.

Supporting checked results include coordinate transposition of paths, a
protected shift bound retaining actual access distance, and blank routing that
only visits the initial column and final row. The generic conjugation lemma
restores routing cells even when the temporary route crosses completed regions.

Preparation is the first completed global phase. Transport's legal realization
and inefficient-move estimate, Arrange, and Finish remain open. Proposition 9
is still conditional on those remaining constructions.

Validation: `lake build` succeeds (8785 jobs). The axiom audit succeeds for 122
declarations, including `exists_preparation_path` and `preparationContract`,
using only `propext`, `Classical.choice`, and `Quot.sound`. The source scan found
no proof placeholders or custom axioms. Upstream and minor local style warnings
remain; there are no proof errors.

## Arrangement phase complete (2026-09-20 continuation)

This checkpoint supersedes the open Arrange items in earlier checkpoints.
Its constants are historical; the 2026-09-22 update above halves the paired
schedule's accounting and propagates that change through the final bounds.
`Algorithm/Arrangement.lean` proves `Partition.exists_arrangement_path` and
`Algorithm.arrangeContract : ArrangeContract 12464`. Given clear corridors and
sorted reservoirs, the constructed path sorts every nonblank tile into its
target square, returns the blank, and restores every reservoir cell exactly.
The path theorem does not require reachability; the contract carries it from
the input, together with the blank's last-reservoir position.

The proof has two schedules:

- `ArrangementVertical.lean`: pair `V(i,j)` with `V(j,i)` for all valid group
  indices. The cost is at most `6232*k^11`, with horizontal corridors and
  reservoirs restored.
- `ArrangementHorizontal.lean`: pair horizontal slices by interchanging their
  row-within-block and column-block indices. The cost is at most `6232*k^10`,
  with vertical corridors and reservoirs restored.

`Moves/ExchangeSchedule.lean` proves the finite involution schedule, including
fixed regions and restoration outside the scheduled regions. `Moves/Exchange.lean`
exchanges arbitrary disjoint nonblank sets of equal size `m >= 2` in at most
`6232*m*n` moves. Two internal buffer cells absorb the parity of odd-size
exchanges; only membership, not internal ordering, is promised.

The underlying `exists_three_cycle` rotates any three distinct nonblank tiles
in at most `3116*n` moves, fixes all other cells, and returns the blank. Its
proof stages only three top-row positions, executes a checked strip rotation,
and undoes staging by relabeling the reverse path. This avoids paying quadratic
row-placement cost per tile. All paths and bounds are in the public model.

Transport and Finish remain open. In particular, this construction does not
assume independent solvability of sorted squares or discharge Finish's parity
and access obligations. Unconditional Proposition 9 is still not claimed.

Validation: the full `lake build` succeeds (8793 jobs). The audit checks 142
declarations, including the arrangement contract and its supporting exchange
lemmas, with only `propext`, `Classical.choice`, and `Quot.sound`. The public
source scan found no proof placeholders or custom axiom declarations.

## Finish phase complete, without recursion (2026-09-20 continuation)

This checkpoint supersedes the earlier open Finish obligations.
`Partition.exists_finish_path` solves every `Arranged` input in at most
`15000*k^11` moves; `Algorithm.finishContract : FinishContract 15000` discharges
the original contract without adding local solvability assumptions.

The construction moves the blank to the global bottom-right corner, then
processes every nonfinal square once. `Moves/BlockFinish.lean` proves that a
closed nonblank square of side `m` can be solved within `2000*m^3+10000*n` moves
on a board of side `n`, restoring the blank and all outside cells except for a
possible exchange of two designated buffer tiles. The local corner is corrected
by a three-cycle. Blank access from the global bottom-right corner touches only
the block's corner; all other block cells stay fixed. The local cubic solver
finishes up to a specified transposition, and reverse relabeled access restores
the global route. Any remaining transposition is paired with a buffer swap.

Both buffer tiles are in the final square. Thus each finished nonfinal square
remains solved, and all square memberships survive. `FinishBlocks.lean` bounds
the full schedule by `12000*k^11`. With every other square solved, the existing
residual construction and reachability theorem establish the final square's
solvability; its direct cubic solution costs at most `2000*k^9`. Initial blank
normalization costs at most `2*k^4`. No recursive subdivision is used.

`PhaseAssembly.lean` proves `phaseContracts_of_transport`,
`fourthPowerApproximation_of_transport`, `uniformApproximation_of_transport`,
and `proposition9_of_transport`. The only remaining hypothesis is
`TransportContract C` for a uniform constant `C`. These remain conditional
results: the count-only transport algorithm has not yet been realized by legal
paths with the required inefficient-move estimate.

Validation: full `lake build` passes (8803 jobs). `Checks/Axioms.lean` audits
168 declarations using only `propext`, `Classical.choice`, and `Quot.sound`,
including the full Finish contract and the reduction to Transport alone.
The public-source scan found no proof placeholders or custom axiom declarations.


## Transport corridor paths and run realization (2026-09-20 continuation)

Transport remains open, but its straight-slide estimate and the count-to-path
composition now have checked proofs.

- `Moves/Corridor.lean`: `exists_increasing_corridor_path` constructs an actual
  legal path along an embedded adjacent line, retaining tile-group membership
  and fixing cells outside the traversed segment. Once the blank passes `cap`,
  every remaining move decreases the standard Manhattan potential; the cost is
  at most `cap-a` inefficient moves. `exists_oriented_corridor_path` specializes
  this to all four grid directions and bounds inefficient moves by the width
  of the target-coordinate interval, when the blank starts in that interval.
- `Algorithm/TransportCorridors.lean`: `exists_group_corridor_path` specializes
  the estimate to target squares, giving `k^3`. The concrete
  `exists_horizontal_transport_slide` implements step (ii) in either direction,
  preserves all nonblank memberships in the corridor, and restores every other
  row. Its input allows the blank in the corridor and does not require Clear.
- `Algorithm/TransportRealization.lean`: `exists_path_of_count_run` lifts an
  abstract count run using explicitly supplied local legal transfers, matches
  the final matrix to the final board, and sums inefficient moves.
  `transportContract_of_step_bound` proves that local budgets `C*k^3` suffice
  for the original Transport contract with budget `C*k^11`.
- `manhattan_blank_swap_balance` exposes the exact moved-tile potential change.
  The existing one-step Manhattan theorem now uses that identity.

**Next:** construct `TransportStepBound hk (C*k^3)` by composing entry and exit
jumps, the horizontal slide, and monotone vertical segments with short jumps
across horizontal bands. Restore Clear and prove the exact matrix update at
iteration boundaries. The vertical budget must telescope across segments;
charging `k^3` independently for every segment loses the required exponent.
The rank-dependent `cap-a` estimate is available for that accounting.
No complete transport construction or unconditional Proposition 9 is claimed.

Validation: `lake build` passes (8806 jobs). `lake env lean Checks/Axioms.lean`
audits 176 declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
The public-source scan found no proof placeholders or custom axiom declarations;
the only textual `admit` match is ordinary prose in an existing doc comment.


## Transport and Proposition 9 complete (2026-09-21)

This checkpoint supersedes all earlier open Transport and final-assembly items.
`Algorithm.transportContract : TransportContract 184` proves the original
contract, with no additional input invariant or unproved local-path hypothesis.
`Proposition9Complete.lean` exports the two unconditional final conclusions
`SlidingPuzzle.average_optimal_length` and `SlidingPuzzle.gods_number`, and the
conjunction `SlidingPuzzle.proposition9`.

The local transfer budget is `184*k^3`:

- Entry and horizontal travel: `exists_transport_horizontal_path`, `26*k^3`.
- Vertical entry, slides, and band crossings: `verticalTransportBound`, `132*k^3`.
- Parity adjustment and exit: `exists_transport_exit_path`, `26*k^3`.

`Moves/Jump.lean` lifts the existing checked strip words in every orientation,
with cost at most `25*(endpoint distance+1)`. The strip is cropped to the actual
endpoint span. These are genuine paths with an exact blank/tile transposition;
no arbitrary transposition is asserted legal. `exists_group_vertical_jump`
uses a neighboring tile from the same group to resolve either checkerboard
parity, at cost `26*(vertical gap+2)`.

`TransportLabels.lean` treats the blank temporarily as a member of the incoming
group. The resulting `GroupEquivalent` relation composes through every operation,
including states whose blank is in a corridor. At the final reservoir endpoint,
it proves Clear and the precise count-matrix update. Individual corridor labels
may permute; their group memberships are what the count argument requires.

`exists_banded_vertical_route` traverses monotone rank intervals. Downward ranks
are ordinary row coordinates; upward ranks use `Fin.rev`. Horizontal bands have
width k; crossings cost at most `26*(k+3)`. The destination band's ordinary slide
costs at most `k^3` inefficient moves. Every subsequent ordinary slide is
strictly efficient. Thus at most k crossings and the initial entry fit within
`132*k^3`; the proof never charges `k^3` independently for each band.

The existing count run has at most `k^8` transfers and is now realized by board
paths. Together with the other phases, the fourth-power solution satisfies
`length ≤ manhattan B + 57374*k^11`. General-size and statistical reductions
then discharge both final asymptotic statements. The imported Zhong sources
remain unchanged. The suggested staircase word is not a dependency of this proof.

Validation: `lake build` succeeds (8816 jobs); `lake env lean Checks/Axioms.lean`
audits 208 declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
The exported final theorem types have no remaining phase hypotheses. All 25
imported source hashes match `ThirdParty/Zhong/SOURCE_HASHES.json`. The public
Lean sources contain no proof placeholders or custom axiom declarations.
