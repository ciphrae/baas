import SlidingPuzzle.Algorithm.PhaseAssembly
import SlidingPuzzle.Algorithm.Parberry.Reduction

/-! Quantitative projections from a genuine local cubic solver. Its legal paths
are threaded through parity repair and all block-finishing operations. The
remaining Parberry layer construction is explicit, never imported as an axiom. -/
namespace SlidingPuzzle.Algorithm

open SlidingPuzzle.Partition

/-- The finishing path budget obtained if each local square can be solved in
`5*m^3` moves while the current `220*k^11` access and buffer budget is kept. -/
def FastFinishPath : Prop :=
  ∀ k : ℕ, ∀ hk : 2 ≤ k,
    letI : NeZero (k^4) := ⟨by positivity⟩
    ∀ B : Board (k^4), Arranged hk B →
      ∃ p : Path B (target (k^4)), p.length ≤ 225*k^11

/-- A genuine five-cubic solver supplies the whole fast Finish construction,
including borrowed blanks, local parity repairs, and the final residual solve. -/
theorem fastFinishPath_of_cubicSolver (h : CubicSolverBound 5) : FastFinishPath := by
  intro k hk
  let : NeZero (k^4) := ⟨by positivity⟩
  intro B hB
  exact exists_finish_path_of_solver h hk B hB

/-- Completing the cheap protected layer routine discharges the solver and
therefore the fast Finish hypothesis. -/
theorem fastFinishPath_of_layer (h : Parberry.LayerPathBound) : FastFinishPath :=
  fastFinishPath_of_cubicSolver (Parberry.cubicSolverBound_of_layer h)

theorem fastFinishContract (h : FastFinishPath) : FinishContract 113 := by
  intro k hk
  letI : NeZero (k^4) := ⟨by positivity⟩
  intro B hB
  obtain ⟨p,hp⟩ := h k hk B hB
  refine ⟨target (k^4),p,rfl,?_⟩
  have hh := p.inefficientMoves_le_half_length
  nlinarith

/-- Replacing only Finish by the projected fast path gives this fourth-power
inefficiency and additive length bound. -/
theorem fourth_power_of_fast_finish (h : FastFinishPath) (k : ℕ) (hk : 2 ≤ k)
    [NeZero (k^4)] (B : Board (k^4)) (hB : Reachable B) :
    ∃ p : Path B (target (k^4)), p.inefficientMoves ≤ 2866*k^11 ∧
      p.length ≤ manhattan B + 5732*k^11 := by
  exact exists_solution_of_phase_bounds preparationContract transportContract k hk
    (h k hk) (by norm_num : 274+225 ≤ 2*1751) B hB

/-- The corresponding arbitrary-dimension upper bound, conditional on the
faster finishing construction. -/
theorem optimalLength_le_of_fast_finish (h : FastFinishPath)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      13764*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  letI : NeZero (k^4) := ⟨by positivity⟩
  have hfourth (A : ReachableBoard (k^4)) :
      optimalLength A ≤ manhattan A.val+5732*k^11 := by
    obtain ⟨p,_,hp⟩ := fourth_power_of_fast_finish h k hk A.val A.property
    exact (optimalLength_le_path_length A p).trans hp
  have hh := optimalLength_le_of_fourth_power_bound_rpow B k 5732 hk hlo hhi hfourth
  norm_num at hh
  exact hh

/-- A shortest witness converts the conditional additive bound to the
corresponding inefficient-move bound. -/
theorem exists_solution_of_fast_finish (h : FastFinishPath)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 6882*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+13764*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength : (p.length : ℝ) ≤
      (manhattan B.val : ℝ)+13764*Real.rpow (n : ℝ) (11/4 : ℝ) := by
    rw [hp]
    exact optimalLength_le_of_fast_finish h hn B
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ) =
      (manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- The five-cubic solver hypothesis now suffices for the arbitrary-size bound;
no separate fast-finishing hypothesis is needed. -/
theorem optimalLength_le_of_cubic_solver (h : CubicSolverBound 5)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      13764*Real.rpow (n : ℝ) (11/4 : ℝ) :=
  optimalLength_le_of_fast_finish (fastFinishPath_of_cubicSolver h) hn B

/-- Legal witnesses and inefficient-move counts derived directly from a
five-cubic solver. -/
theorem exists_solution_of_cubic_solver (h : CubicSolverBound 5)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 6882*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+13764*Real.rpow (n : ℝ) (11/4 : ℝ) :=
  exists_solution_of_fast_finish (fastFinishPath_of_cubicSolver h) hn B

end SlidingPuzzle.Algorithm
