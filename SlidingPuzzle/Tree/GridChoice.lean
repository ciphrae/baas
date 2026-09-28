import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace SlidingPuzzle.Tree

/-- All sufficiently large integer sizes admit an even branching value in a
multiplicative factor-two window. -/
theorem exists_even_branching_grid (D : ℕ) (hD : 1 ≤ D) (B : ℕ) (hB : 2 ≤ B)
    (n : ℕ) (hn : (2 * B) ^ D ≤ n) :
    ∃ b : ℕ, B ≤ b ∧ Even b ∧ b ^ D ≤ n ∧ n ≤ (2 * b) ^ D := by
  let x : ℝ := (n : ℝ) ^ (1 / (D : ℝ))
  let q := Nat.floor (x / 2)
  let b := 2 * q
  have hD : 0 < D := by omega
  have hn0 : (0 : ℝ) < n := by
    have hp : 0 < (2 * B) ^ D := by positivity
    exact_mod_cast (lt_of_lt_of_le hp hn)
  have hx : x ^ D = (n : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    rw [show (1 / (D : ℝ)) * (D : ℝ) = 1 by field_simp, Real.rpow_one]
  have hxlo : 2 * (B : ℝ) ≤ x := by
    have hp : (2 * (B : ℝ)) ^ D ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ (2 * (B : ℝ)) ^ D by positivity) hp
      (show 0 ≤ 1 / (D : ℝ) by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (2 * (B : ℝ)) by positivity)] at hpow
    rw [show (D : ℝ) * (1 / (D : ℝ)) = 1 by field_simp, Real.rpow_one] at hpow
    exact hpow
  have hqlo : x / 2 - 1 < (q : ℝ) := by
    dsimp [q]
    have := Nat.lt_floor_add_one (x / 2)
    linarith
  have hqhi : (q : ℝ) ≤ x / 2 := by dsimp [q]; exact Nat.floor_le (by linarith)
  have hbcast : (b : ℝ) = 2 * (q : ℝ) := by simp [b]
  have hBreal : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hbge : (B : ℝ) ≤ b := by
    rw [hbcast]
    have : (B : ℝ) - 1 ≤ (q : ℝ) := by linarith [hxlo]
    nlinarith [hBreal]
  have hblo : x ≤ 2 * (b : ℝ) := by rw [hbcast]; nlinarith [hqlo, hBreal]
  have hbhi : (b : ℝ) ≤ x := by rw [hbcast]; linarith [hqhi]
  have hnatlo : B ≤ b := by exact_mod_cast hbge
  have hrealpowlo : (b : ℝ) ^ D ≤ (n : ℝ) := by
    rw [← hx]
    exact pow_le_pow_left₀ (by positivity) hbhi D
  have hrealpowhi : (n : ℝ) ≤ (2 * (b : ℝ)) ^ D := by
    calc
      (n : ℝ) = x ^ D := hx.symm
      _ ≤ (2 * (b : ℝ)) ^ D := pow_le_pow_left₀ (by positivity) hblo D
  refine ⟨b, hnatlo, ?_, ?_, ?_⟩
  · refine ⟨q, ?_⟩
    simp [b, Nat.two_mul]
  · exact_mod_cast hrealpowlo
  · exact_mod_cast hrealpowhi


/-- The tree term for a grid `b^(2h+1) ≍ n`: if `n ≤ A (2b)^(2h+1)` with `A ≥ 1`, then
`n³/b^h ≤ A 2^h n^(5/2 + 1/(4h+2))`. -/
theorem grid_tree_cost_odd (h : ℕ) (n b : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hhi : (n : ℝ) ≤ A * (2 * (b : ℝ)) ^ (2 * h + 1)) (hb : 0 < b) (hn : 0 < n) :
    (n : ℝ) ^ 3 / (b : ℝ) ^ h ≤
      A * 2 ^ h * (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  set α : ℝ := (h : ℝ) / (2 * (h : ℝ) + 1) with hαdef
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α ≤ 1 := by
    rw [hαdef, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hmono := Real.rpow_le_rpow (by positivity) hhi hα0
  rw [Real.mul_rpow (by positivity) (by positivity)] at hmono
  have hpowEq : ((2 * (b : ℝ)) ^ (2 * h + 1)) ^ α = (2 * (b : ℝ)) ^ h := by
    rw [← Real.rpow_natCast (2 * (b : ℝ)) (2 * h + 1),
      ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
    congr 1
    rw [hαdef]; push_cast; field_simp
  rw [hpowEq, mul_pow] at hmono
  have hAα : A ^ α ≤ A := by
    calc A ^ α ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA hα1
      _ = A := Real.rpow_one A
  have hroot : (n : ℝ) ^ α ≤ A * 2 ^ h * (b : ℝ) ^ h := by
    calc (n : ℝ) ^ α ≤ A ^ α * (2 ^ h * (b : ℝ) ^ h) := hmono
      _ ≤ A * (2 ^ h * (b : ℝ) ^ h) := mul_le_mul_of_nonneg_right hAα (by positivity)
      _ = _ := by ring
  have hsplit : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 - α) * (n : ℝ) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  have hexp : 3 - α = 5 / 2 + 1 / (4 * (h : ℝ) + 2) := by
    rw [hαdef]
    field_simp
    ring
  rw [hsplit, ← hexp, div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (3 - α))
  nlinarith [this]

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
