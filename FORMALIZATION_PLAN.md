# Proposition 9: formalization and agent handoff

## Goal and completion standard

Formalize Proposition 9 and its proof from Zhixian Zhong, *Additive Approximation Algorithms for Sliding Puzzle* (2023), Section 5.2, printed page 145 (PDF page 17). The source is `zhong2023_additive-approximation-sliding-puzzle.pdf` in this directory.

Use Lean 4 and mathlib. The workspace initially contained only the paper. A Lean project has since been implemented with Lean `4.33.1` and pinned mathlib; see `STATUS.md` for checked declarations and validation. The completion standard below is now met by the unconditional exports in `Proposition9Complete.lean`.

The final results concern the uniform average and the maximum of shortest solution lengths over the **reachable orbit of the standard target**, not all permutations:

* `average_optimal_length n - (2 / 3 : ℝ) * (n : ℝ)^3 = O((n : ℝ)^(11 / 4 : ℝ))`;
* `gods_number n - (n : ℝ)^3 = O((n : ℝ)^(11 / 4 : ℝ))`.

Use `Asymptotics.IsBigO Filter.atTop` on functions `ℕ → ℝ`, with `Real.rpow` for the fractional exponent. Define the functions to be zero for `n < 2`, or use an equivalent extension agreed at the interface milestone. Prove that the eventual statements only use valid sizes.

Completion means a reproducible `lake build`, both theorems instantiated for the concrete puzzle, no `sorry`, `admit`, custom axioms, or unresolved hypotheses standing in for mathematical dependencies. Standard Lean/mathlib logical axioms are acceptable. An intermediate conditional theorem is useful, but is not completion.

## Completion checkpoint (updated 2026-09-22)

All mathematical construction obligations are discharged. The public exports
`SlidingPuzzle.average_optimal_length`, `SlidingPuzzle.gods_number`, and
`SlidingPuzzle.proposition9` have no algorithmic or statistical hypotheses.

The current four contract constants are `1033`, `82`, `3277`, and `374` for
Preparation, Transport, Arrangement, and Finish. The exact count algorithm is
realized by legal paths with `82*k^3` inefficient moves per transfer and at
most `k^8` transfers. `Algorithm.exists_fourth_power_solution` combines
arrangement and finishing before halving their joint length, giving additive term `6254*k^11`; the arbitrary-size bound is
`14286*n^(11/4)`. `Algorithm.uniformApproximation` instantiates the general-size
reduction, and `Proposition9Complete.lean` finishes the statistical conclusions.

The source below retains the original work plan and acceptance criteria as a
record of the proof's organization. Historical conditional theorems remain
available as reusable reductions; the final exports instantiate all of them.
No recursive subdivision is used in Finish, and local parity repair and blank
access are included in its bound.

Imported source is limited to checked concrete lemmas with proved compatibility;
old phase modules, unfinished availability assumptions, and claims of
impossibility remain excluded. See `ThirdParty/Zhong/NOTICE.md`, `STATUS.md`,
and `PROOF_NOTES.md` for the dependency and proof-to-paper records.

## Working protocol

1. Read applicable repository instructions before editing. Pin a compatible Lean/mathlib pair and record it; do not assume a particular library lemma exists before checking the installed source.
2. Keep a `STATUS.md` with each work package's owner, status, exported declarations, validation command, and outstanding obligations. Record mathematical discrepancies in `PROOF_NOTES.md`, with paper page references and their resolutions.
3. Freeze shared definitions and theorem signatures after package A. Downstream agents import these files; they do not create competing definitions of boards, moves, or OPT.
4. Give each agent exclusive ownership of its assigned files. Shared-interface changes go through the integration owner. Parallelize only packages whose interfaces are already stable.
5. Prove explicit finite inequalities first. Convert to asymptotic statements at module boundaries. Constants must be independent of both the board and the dimension.
6. Every handoff includes changed files, exact exported theorem names, a successful check command, remaining assumptions, and any departure from the printed argument.
7. If a paper claim fails, give a counterexample or precise missing hypothesis and repair it with a proved replacement sufficient for Proposition 9. Never conceal the gap behind an axiom or change the final theorem's meaning.

## Suggested modules and dependency graph

```text
SlidingPuzzle/Basic.lean
SlidingPuzzle/Paths.lean
SlidingPuzzle/OrbitParity.lean
SlidingPuzzle/Manhattan.lean
SlidingPuzzle/Statistics.lean
SlidingPuzzle/DistanceEstimates.lean
SlidingPuzzle/Moves/Local.lean
SlidingPuzzle/Moves/Placement.lean
SlidingPuzzle/Algorithm/Partition.lean
SlidingPuzzle/Algorithm/Build.lean
SlidingPuzzle/Algorithm/Transport.lean
SlidingPuzzle/Algorithm/Arrangement.lean
SlidingPuzzle/Algorithm/Finish.lean
SlidingPuzzle/Algorithm/GeneralSize.lean
SlidingPuzzle/Asymptotics.lean
SlidingPuzzle/Proposition9.lean
```

`Basic → Paths → Manhattan`; `Basic + Paths → OrbitParity`; `Paths → Statistics`; `OrbitParity + Manhattan → DistanceEstimates`; `Paths → Local + Placement`; these feed the algorithm modules in phase order. `Statistics + Manhattan + DistanceEstimates + GeneralSize + Asymptotics → Proposition9`.

These names are intended ownership boundaries; small modules may be merged by agreement.

## A. Foundations and interface freeze

**Owner:** integration/foundations agent.

Represent cells by `Fin n × Fin n`, tiles by `Fin (n*n)`, and a board by an equivalence from cells to tiles. Tile zero is the blank. Define the row-major standard target with zero in the bottom-right cell. For `n ≥ 2`, define:

* the blank position and the position of each tile;
* a legal step as swapping the blank with a cell at grid distance one;
* legal finite paths, their length, concatenation, reversal, and endpoints;
* `ReachableBoard n` as boards reachable from the target;
* `optimalLength` on reachable boards, with an actual shortest-path witness;
* `manhattan` as the sum of tile distances **excluding zero**;
* real-valued finite averages and maxima over the orbit.

Use a noncomputable finite construction if useful; efficient enumeration of the orbit is not required. A graph-distance default on disconnected vertices must not accidentally define OPT for unsolvable states. Prove finiteness and nonemptiness of the orbit, including target membership.

Required API: reverse/append paths, `optimalLength_le_path_length`, shortest witness, target Manhattan zero, finite-average monotonicity, maximum attainment and monotonicity. State one common uniform approximation interface, schematically:

```text
∃ C ≥ 0, ∃ N, ∀ n ≥ N, ∀ B : ReachableBoard n,
  (optimalLength B : ℝ) ≤ manhattan B + C * (n : ℝ)^(11/4 : ℝ)
```

**Acceptance:** foundation files compile; statistics refer to reachable boards; exact downstream signatures are recorded in `STATUS.md`.

## B. Manhattan potential and finite transfer lemmas

**Owner:** potential/statistics agent; starts after A.

Prove each legal move changes integer Manhattan distance by `+1` or `-1`. Define inefficient moves as the increasing moves. For a path from B to the target prove the exact identity

```text
length = manhattan B + 2 * inefficientCount.
```

Deduce `manhattan B ≤ optimalLength B`. Prove the general average and maximum sandwich: a board-independent `D ≤ OPT ≤ D + E` implies the same inequalities for averages and maxima. These finite results should have no asymptotic prerequisites.

**Caution:** Section 5 writes an overhead of α for α inefficient moves, whereas Proposition 5 has `2α`. Keep the factor two in finite lemmas; absorb it only in Big-O bounds.

**Acceptance:** compiled exact path identity and average/maximum transfer theorems; no imported approximation assumption needed for the lower bound.

## C. Orbit parity and distance estimates

**Owner:** combinatorics agent; starts after A and coordinates with B.

Formalize the solvability criterion needed from Proposition 3, including sufficiency, or prove concrete reachability symmetries sufficient for every use below. An invariant alone does not establish reachability.

Prove the two estimates cited from Parberry [2] in Proposition 9. First inspect the original reference if available (Ian Parberry, *A real-time algorithm for the (n²−1)-puzzle*, 1995). A citation is not a formal proof. Independent proofs of these estimates are acceptable and should be documented as replacements for the citation.

### Mean distance

Prove each fixed nonblank tile has a uniform position in the reachable orbit. A possible route is to pair the two parity classes of all boards with a fixed tile position by swapping two other nonblank labels. Show the pairing preserves the fixed position and changes solvability class; prove all required cardinality and small-size conditions. Do not infer uniformity merely from all permutations being uniform.

Exchange finite sums and evaluate the one-dimensional distance sum. A useful candidate stronger identity to prove, after proving uniform marginals, is

```text
averageManhattan n = (2/3 : ℝ) * n^3 - (5/3 : ℝ) * n + 1  (n ≥ 2).
```

Here the total contribution of all target cells is `(2/3) * (n^3 - n)`, and removing the corner blank's contribution subtracts `n - 1`. Check the identity independently before adopting it as an interface. The required export is only an absolute error bounded by `C*n^2` eventually.

### Maximum lower bound

Start with the board whose tile positions are the half-turn images of their targets. Evaluate its Manhattan distance. If it is not reachable, swap two nonblank tiles to correct parity using the proved criterion. Bound the distance loss by `O(n)` (an `O(n²)` bound suffices). Prove reachability of the resulting board; do not assume the uncorrected half-turn board is solvable for every n.

### Maximum upper bound: follow the printed proof

Use the center `c = ((n : ℝ)-1)/2` and the triangle inequality. Add the nonnegative blank contribution to bound the sum by

```text
4*n * ∑ x : Fin n, |(x : ℝ) - c|.
```

Prove this expression equals `n^3` for even n and `n^3-n` for odd n. Export `manhattan B ≤ n^3`, and hence the maximum upper bound.

**Acceptance:** compiled mean error bound, reachable maximum lower bound, and upper bound; every use of parity justified. Check small sizes by finite computations as diagnostics, not substitutes for general proofs.

## D. Local move and placement library

**Owner:** algorithm foundations agent; starts after A.

Read Sections 2.2–2.3 and 4.1, including figures and the displayed words in Lemmas 1–2. Render the pages when extraction is ambiguous. The paper's U/D/L/R are **tile directions**, opposite to blank motion; choose and document one convention, with a translation lemma if needed.

Prove legal application, resulting permutation, preserved cells, blank endpoint, and an explicit length bound for:

* moves embedded into rectangular subboards; inverse words and conjugation;
* row/column translation (Lemma 1), including its width hypotheses;
* parity-compatible blank/tile swaps in two-row or two-column strips (Lemma 2), all orientations and boundary cases;
* tile placement with protected solved cells, giving the bounds used from Proposition 4;
* a constructive solver with `O(m^3)` moves for solvable m-by-m blocks;
* exchanges of strips through setup, local operation, and inverse setup, with preservation outside the intended support.

Do not prove only that some path exists: later packages need uniform quantitative bounds and preservation guarantees. Abstract helper contracts may be used during development, but must be instantiated by proved constructions.

**Acceptance:** compiled local operations and protected-placement APIs sufficient for all four phases. Record any corrected move words and why they are correct.

## E. Fourth-power algorithm and quantitative proof

**Owner:** algorithm agent(s), with separate files per phase. Depends on B and D.

For `n = k^4`, `k ≥ 2`, formalize Section 4.1. First define the target tile groups and H/V/R cell partition, prove disjointness, coverage and cardinalities, and define clear state and the reservoir invariant.

**Resolve a literal issue before freezing these predicates:** the paper defines S groups as nonzero tiles, but writes `Ri ⊆ Si` at termination even though some R region contains zero. State containment for nonblank tiles, with a separate blank-location invariant. Check all cardinality arguments under this correction.

Phase contracts must expose input/output invariants, a legal path witness, and an explicit inefficient-move bound `≤ C_phase * k^11` with constants independent of k and the input board. Bounds on all moves imply bounds on inefficient moves where appropriate.

1. **Build:** formalize selected-tile capacities, placement, translations, clear state, and one representative of each nonfinal group in the last reservoir. Prove choices exist and earlier placements remain valid.
2. **Transport:** implement Algorithm 4 or a proved equivalent. Prove the count matrix agrees with the board, the off-diagonal sum decreases, and termination occurs within `k^8` iterations. Preserve the minimum-index choice: the paper uses it in the termination-to-sortedness argument. Prove the reservoir exhaustion argument, legal jumps, and that long transport segments outside the destination block are efficient. Bound inefficient moves per iteration by `O(k^3)` and the total by `O(k^11)`; a crude bound on all moves is insufficient.
3. **Arrange (complete):** `arrangeContract` puts nonblank tiles into their target squares within `3277*k^11` legal moves. Checked paired-region schedules exchange vertical corridors and horizontal slices; the blank returns and every reservoir cell is restored. The generic exchange handles odd set sizes with an internal parity correction.
4. **Finish (complete):** `finishContract` solves arranged boards within `15000*k^11` moves without recursive subdivision. Each nonfinal block is solved by the cubic solver with borrowed blank access and a parity correction paired with two final-square buffer tiles. The last square is solved using the existing residual-reachability theorem.

Combine the phase bounds with B's exact identity to export a path of length at most `D(B) + C*k^11`. The polynomial running-time claim is not required for Proposition 9; constructing paths and proving their move bounds is required.

**Acceptance:** a closed fourth-power approximation theorem with no abstract phase assumptions remaining.

## F. General dimensions and asymptotics

**Owner:** integration/asymptotics agent. Arithmetic helpers can start after A; the final approximation theorem depends on E.

Choose integer k with `k^4 ≤ n < (k+1)^4`, eventually `k ≥ 2`. Prove `n-k^4 ≤ C*k^3` and `k^11 ≤ (n : ℝ)^(11/4 : ℝ)` with all casts and nonnegativity hypotheses explicit.

Use protected placement to solve the outer rows/columns in `O((n-k^4)*n^2)` moves, leaving a reachable, correctly labeled residual block. Its Manhattan potential agrees with the remaining global potential after placement. Bound potential increase during the prefix by its length; account for this when combining the residual solution (a factor two in the prefix overhead is harmless). Do not equate the initial potential with the residual potential without justification.

Export the uniform approximation interface from A. Prove `n^2 = O(n^(11/4))` and the required Big-O addition/sandwich lemmas. An equivalent explicit polynomial inequality followed by conversion to `Real.rpow` is acceptable.

**Acceptance:** general-size bound for all sufficiently large n, not merely a fourth-power subsequence; constants uniform over the reachable orbit.

## G. Proposition 9 assembly and final audit

**Owner:** integration agent.

First prove a conditional assembly theorem from the uniform approximation, mean distance error, and maximum distance bounds. This can happen before E finishes and validates the interfaces. Then instantiate every hypothesis with B–F and export the two unconditional theorems, plus an optional conjunction named `proposition9`.

Final checklist:

* `lake build` succeeds with the pinned toolchain and dependency revision.
* Search project source for `sorry`, `admit`, `axiom`, and placeholder assumptions; inspect every hit.
* Run `#print axioms` on both final theorems and inspect the output for unexpected axioms, especially `sorryAx`.
* Inspect final theorem types: concrete puzzle, reachable uniform distribution, correct target, blank excluded, shortest length and maximum, exponent 11/4, all dimensions eventually.
* Check the final dependency chain includes proved local moves, phase bounds, general-size reduction, and parity facts. A theorem parameterized by the missing algorithm is not a completed Proposition 9.
* Add a README mapping paper results to Lean declarations, giving build commands and explaining repairs or alternative proofs. Update `STATUS.md` so no required package remains open.

## Scheduling and milestones

With four agents available: use one integration/foundations owner, one combinatorics owner, one local-moves owner, and one potential/algorithm owner. Begin with A; once interfaces are stable, run B, C, and D independently while integration prepares the conditional assembly and arithmetic. Reassign completed owners to E's separate phases after partition and local-operation APIs stabilize. Integrate F and G last.

Milestones, in order:

1. Compiling puzzle definitions and frozen interfaces.
2. Compiling conditional Proposition 9 and Manhattan statistics, with missing dependencies explicitly tracked.
3. Verified local move library and fourth-power solver bound.
4. General-size uniform bound and unconditional Proposition 9.
5. Clean build, axiom audit, and proof-to-paper documentation.

The critical path is the constructive algorithm proof, now solely Transport. Do not declare the task complete at milestone 2. If blocked, leave a precise failing obligation and reproducible diagnostic so the next agent can continue without rediscovering the issue.
