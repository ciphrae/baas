import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace SlidingPuzzle.Tree

/-- All sufficiently large integer sizes admit an even branching value in a
multiplicative factor-two window. -/
theorem exists_even_branching_grid (h : ℕ) (hh : 1 ≤ h) (B : ℕ) (hB : 2 ≤ B)
    (n : ℕ) (hn : (2 * B) ^ (2 * h + 2) ≤ n) :
    ∃ b : ℕ, B ≤ b ∧ Even b ∧ b ^ (2 * h + 2) ≤ n ∧
      n ≤ (2 * b) ^ (2 * h + 2) := by
  let D := 2 * h + 2
  let x : ℝ := (n : ℝ) ^ (1 / (D : ℝ))
  let q := Nat.floor (x / 2)
  let b := 2 * q
  have hD : 0 < D := by dsimp [D]; omega
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


/-- The upper grid edge bounds the real power of the chosen grid size. -/
theorem grid_power_lower_bound (h : ℕ) (hh : 1 ≤ h) (n b : ℕ)
    (hb : 0 < b) (hhi : n ≤ (2 * b) ^ (2 * h + 2)) :
    (n : ℝ) ^ ((h : ℝ) / (2 * (h : ℝ) + 2)) ≤
      (2 : ℝ) ^ h * (b : ℝ) ^ h := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hupper : (n : ℝ) ≤ (2 * (b : ℝ)) ^ (2 * h + 2) := by
    exact_mod_cast hhi
  have hα : 0 ≤ (h : ℝ) / (2 * (h : ℝ) + 2) := by positivity
  have hmono := Real.rpow_le_rpow (show (0 : ℝ) ≤ n by positivity) hupper hα
  have hexp : (2 * (h : ℝ) + 2) * ((h : ℝ) / (2 * (h : ℝ) + 2)) = (h : ℝ) := by
    have hd : 2 * (h : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  have hpowEq : ((2 * (b : ℝ)) ^ (2 * h + 2)) ^
      ((h : ℝ) / (2 * (h : ℝ) + 2)) = (2 * (b : ℝ)) ^ h := by
    rw [← Real.rpow_natCast (2 * (b : ℝ)) (2 * h + 2)]
    rw [← Real.rpow_mul (le_of_lt (show 0 < 2 * (b : ℝ) by positivity))]
    push_cast
    rw [hexp, Real.rpow_natCast]
  rw [hpowEq] at hmono
  rw [mul_pow] at hmono
  exact hmono

/-- The tree term has the claimed exponent for every grid choice in the
factor-two interval. -/
theorem grid_tree_cost (h : ℕ) (hh : 1 ≤ h) (n b : ℕ)
    (hlo : b ^ (2 * h + 2) ≤ n) (hhi : n ≤ (2 * b) ^ (2 * h + 2))
    (hb : 0 < b) :
    (n : ℝ) ^ 3 / (b : ℝ) ^ h ≤
      (2 : ℝ) ^ h * (n : ℝ) ^ (5 / 2 + 1 / (2 * (h : ℝ) + 2)) := by
  have hn0 : (0 : ℝ) < n := by
    have hnNat : 0 < n := lt_of_lt_of_le (pow_pos hb (2 * h + 2)) hlo
    exact_mod_cast hnNat
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  let α : ℝ := (h : ℝ) / (2 * (h : ℝ) + 2)
  have hroot : (n : ℝ) ^ α ≤ (2 : ℝ) ^ h * (b : ℝ) ^ h := by
    simpa [α] using grid_power_lower_bound h hh n b hb hhi
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hsplit : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 - α) * (n : ℝ) ^ α := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hn0]
    congr 1
    dsimp [α]
    ring
  have hdiv : (n : ℝ) ^ α / (b : ℝ) ^ h ≤ (2 : ℝ) ^ h := by
    apply (div_le_iff₀ (by positivity : 0 < (b : ℝ) ^ h)).2
    calc
      (n : ℝ) ^ α ≤ (2 : ℝ) ^ h * (b : ℝ) ^ h := hroot
      _ = (2 : ℝ) ^ h * (b : ℝ) ^ h := rfl
  have hcost : (n : ℝ) ^ 3 / (b : ℝ) ^ h ≤
      (2 : ℝ) ^ h * (n : ℝ) ^ (3 - α) := by
    rw [hsplit]
    calc
      (n : ℝ) ^ (3 - α) * (n : ℝ) ^ α / (b : ℝ) ^ h =
          (n : ℝ) ^ (3 - α) * ((n : ℝ) ^ α / (b : ℝ) ^ h) := by ring
      _ ≤ (n : ℝ) ^ (3 - α) * (2 : ℝ) ^ h :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (2 : ℝ) ^ h * (n : ℝ) ^ (3 - α) := by ring
  have hexp : 3 - α = 5 / 2 + 1 / (2 * (h : ℝ) + 2) := by
    dsimp [α]
    have hd : 2 * (h : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp] at hcost
  exact hcost

/-- Fixed integer depths make the exponent arbitrarily close to `5/2`. -/
theorem exists_depth_for_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℕ, 1 ≤ h ∧ 5 / 2 + 1 / (2 * (h : ℝ) + 2) ≤ 5 / 2 + ε := by
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
  have hd : 0 < 2 * (h : ℝ) + 2 := by positivity
  have hfrac : 1 / (2 * (h : ℝ) + 2) ≤ ε := by
    apply (div_le_iff₀ hd).2
    nlinarith [hlarge]
  linarith


end SlidingPuzzle.Tree
