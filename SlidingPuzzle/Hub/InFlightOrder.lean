import SlidingPuzzle.Hub.InFlightRound
import SlidingPuzzle.Hub.ChernoffPerm

/-! # A good order of the rounds exists

For every half `H`, distance `d < k`, class `x` and start time `τ0`, the orders
violating the window property (A) (few pushes in `(τ0, τ0 + w_d]`) or (B) (many
`(H, d, x)` insertions in `[τ0, τ0 + w_d]`) are at most a `2^(-λ)` fraction of all
orders (`card_badA`, `card_badB`, by the permutation Chernoff bounds). The
number of events is below `2^λ`, so some order avoids all of them
(`exists_good_sigma`). -/
namespace SlidingPuzzle.Hub

open Finset

variable {k Δ : ℕ} (s : ℕ) (rs : Fin Δ → Round k)

/-- The times `(τ0, τ0 + w]`. -/
def winA (Δ τ0 w : ℕ) : Finset (Fin Δ) := univ.filter fun τ => τ.val ∈ Ioc τ0 (τ0 + w)

/-- The times `[τ0, τ0 + w]`. -/
def winB (Δ τ0 w : ℕ) : Finset (Fin Δ) := univ.filter fun τ => τ.val ∈ Icc τ0 (τ0 + w)

theorem card_winA {τ0 w : ℕ} (h : τ0 + w < Δ) : (winA Δ τ0 w).card = w := by
  rw [winA, card_fin_filter_mem, filter_true_of_mem (fun i hi => by rw [mem_Ioc] at hi; omega),
    Nat.card_Ioc]
  omega

theorem card_winB_le (τ0 w : ℕ) : (winB Δ τ0 w).card ≤ w + 1 := by
  rw [winB, card_fin_filter_mem]
  exact (card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)

theorem insPos_add_one_ge (H : RowH k) (d : ℕ) : s - k ≤ insPos k s H d + 1 := by
  have : s ≤ (d + 1) * s := Nat.le_mul_of_pos_left s (by omega)
  unfold insPos; split <;> omega

/-- Orders violating (A) at `(H, d, τ0)`. -/
noncomputable def badA (H : RowH k) (d : ℕ) (τ0 : Fin Δ) : Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => τ0.val + win s rs H d < Δ ∧
    ∑ τ ∈ winA Δ τ0.val (win s rs H d), gcnt rs H d (σ τ) < insPos k s H d + 1

/-- Orders violating (B) at `(H, d, x, τ0)`. -/
noncomputable def badB (n : ℕ) (H : RowH k) (d : ℕ) (x : Sq k) (τ0 : Fin Δ) :
    Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => Nb s rs n H d x < ∑ τ ∈ winB Δ τ0.val (win s rs H d), acnt rs H d x (σ τ)

/-- `x < (x / b + 1) * b` as reals. -/
theorem nat_div_add_one_gt (x b : ℕ) (hb : 0 < b) : (x : ℝ) / b < ((x / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := x) hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have : (x : ℝ) < ((x / b : ℕ) : ℝ) * b + b := by exact_mod_cast h
  linarith

theorem card_badA {lam : ℕ} (hk : 0 < k) (hlam : 6 * k * lam ≤ s - k) (H : RowH k) (d : ℕ)
    (τ0 : Fin Δ) : (badA s rs H d τ0).card * 2 ^ lam ≤ Δ.factorial := by
  set w := win s rs H d with hw
  set p := insPos k s H d with hp
  set B := Btot rs H d with hB
  -- trivial cases: the window does not fit
  by_cases hfit : τ0.val + w < Δ
  swap
  · have : badA s rs H d τ0 = ∅ := by
      rw [badA, filter_eq_empty_iff]; intro σ _ h; exact hfit h.1
    rw [this]; simp
  have hB0 : B ≠ 0 := by
    intro h0
    have : w = Δ := by rw [hw, win, if_pos h0]
    omega
  have hwdef : w = 2 * (p + 1) * Δ / B + 1 := by
    have : w = min Δ (2 * (p + 1) * Δ / B + 1) := by rw [hw, win, if_neg hB0]
    rw [this] at hfit ⊢
    rcases min_choice Δ (2 * (p + 1) * Δ / B + 1) with h | h
    · rw [h] at hfit; omega
    · exact h
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τ0.isLt
  have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
  have hkey : 2 * (p + 1) * Δ < w * B := by
    rw [hwdef, add_mul, one_mul]; exact Nat.lt_div_mul_add hBpos
  -- Chernoff
  set g : Fin Δ → ℝ := fun j => (gcnt rs H d j : ℝ) with hg
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hg0 : ∀ j, 0 ≤ g j := fun j => Nat.cast_nonneg _
  have hgK : ∀ j, g j ≤ k := fun j => by
    simp only [hg]; exact_mod_cast countP_half_le (rs j) H (fun p => d ≤ p.2.1)
  have hcard : (Fintype.card (Fin Δ)) = Δ := Fintype.card_fin Δ
  have hT := card_winA (Δ := Δ) hfit
  have hsumg : ∑ j, g j = B := by simp only [hg, hB, Btot]; push_cast; rfl
  have hch := card_lower_tail (winA Δ τ0.val w) g hkR hg0 hgK (by rw [hcard]; exact hΔ)
  rw [hT, hsumg, hcard] at hch
  set μ : ℝ := (w : ℝ) * B / Δ with hμ
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hμgt : 2 * ((p : ℝ) + 1) < μ := by
    rw [hμ, lt_div_iff₀ hΔR]; exact_mod_cast hkey
  have hsub : badA s rs H d τ0 ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      ∑ τ ∈ winA Δ τ0.val w, g (σ τ) ≤ μ / 2 := by
    intro σ hσ
    simp only [badA, mem_filter, mem_univ, true_and] at hσ ⊢
    have h1 : ∑ τ ∈ winA Δ τ0.val w, g (σ τ) ≤ p := by
      simp only [hg]; exact_mod_cast Nat.lt_succ_iff.mp hσ.2
    linarith
  have hc1 : ((badA s rs H d τ0).card : ℝ) ≤ Δ.factorial * Real.exp (-μ / (12 * k)) :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans hch
  -- `2^λ ≤ exp(μ / (12 k))`
  have hnat : 6 * k * lam ≤ p + 1 := hlam.trans (insPos_add_one_ge s H d)
  have hlamR : 6 * (k : ℝ) * lam ≤ p + 1 := by exact_mod_cast hnat
  have h2lam : (2 : ℝ) ^ lam ≤ Real.exp (μ / (12 * k)) := by
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    calc (2 : ℝ) ^ lam = Real.exp (lam * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
      _ ≤ Real.exp (μ / (12 * k)) := by
          apply Real.exp_le_exp.mpr
          rw [le_div_iff₀ (by positivity)]
          have : (lam : ℝ) * Real.log 2 ≤ lam := by
            have := Nat.cast_nonneg (α := ℝ) lam
            nlinarith
          nlinarith
  have hfin : ((badA s rs H d τ0).card : ℝ) * 2 ^ lam ≤ Δ.factorial := by
    calc ((badA s rs H d τ0).card : ℝ) * 2 ^ lam
        ≤ Δ.factorial * Real.exp (-μ / (12 * k)) * Real.exp (μ / (12 * k)) := by
          gcongr
      _ = Δ.factorial := by
          rw [mul_assoc, ← Real.exp_add]; simp [neg_div]
  exact_mod_cast hfin

end SlidingPuzzle.Hub
