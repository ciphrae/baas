import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace SlidingPuzzle.Tree

/-- Fixed integer depths make the exponent arbitrarily close to `5/2`. -/
theorem exists_depth_for_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℕ, 1 ≤ h ∧ 5 / 2 + 1 / (4 * (h : ℝ) + 2) ≤ 5 / 2 + ε := by
  obtain ⟨h, hh⟩ := exists_nat_gt (1 / ε + 1)
  have hpos : 0 < (h : ℝ) := by
    have : 0 < 1 / ε := by positivity
    linarith
  have hlarge : 1 < (h : ℝ) * ε := by
    have hdiv := (div_lt_iff₀ hε).mp (by linarith : 1 / ε < (h : ℝ))
    nlinarith
  have hge : 1 ≤ h := by
    have : 0 < 1 / ε := by positivity
    exact_mod_cast (show (1 : ℝ) ≤ (h : ℝ) by linarith)
  refine ⟨h, hge, ?_⟩
  have hd : 0 < 4 * (h : ℝ) + 2 := by positivity
  have hfrac : 1 / (4 * (h : ℝ) + 2) ≤ ε := by
    apply (div_le_iff₀ hd).2
    nlinarith [hlarge]
  linarith


end SlidingPuzzle.Tree
