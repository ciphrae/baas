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

/-- Orders violating (A) at `(H, d, τ0)`. -/
noncomputable def badA (H : RowH k) (d : ℕ) (τ0 : Fin Δ) : Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => τ0.val + win s rs H d < Δ ∧
    ∑ τ ∈ winA Δ τ0.val (win s rs H d), gcnt rs H d (σ τ) < s

/-- Orders violating (B) at `(H, d, x, τ0)`. -/
noncomputable def badB (n : ℕ) (H : RowH k) (d : ℕ) (x : Sq k) (τ0 : Fin Δ) :
    Finset (Equiv.Perm (Fin Δ)) :=
  univ.filter fun σ => Nb s rs n H d x < ∑ τ ∈ winB Δ τ0.val (wsum s rs H d), acnt rs H d x (σ τ)

/-- `x < (x / b + 1) * b` as reals. -/
theorem nat_div_add_one_gt (x b : ℕ) (hb : 0 < b) : (x : ℝ) / b < ((x / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := x) hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have : (x : ℝ) < ((x / b : ℕ) : ℝ) * b + b := by exact_mod_cast h
  linarith

theorem card_badA {lam : ℕ} (hk : 0 < k) (hlam : 16 * k * lam ≤ s) (H : RowH k) (d : ℕ)
    (τ0 : Fin Δ) : (badA s rs H d τ0).card * 2 ^ lam ≤ Δ.factorial := by
  set w := win s rs H d with hw
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
  have hwdef : w = 4 * s * Δ / (3 * B) + 1 := by
    have : w = min Δ (4 * s * Δ / (3 * B) + 1) := by rw [hw, win, if_neg hB0]
    rw [this] at hfit ⊢
    rcases min_choice Δ (4 * s * Δ / (3 * B) + 1) with h | h
    · rw [h] at hfit; omega
    · exact h
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τ0.isLt
  have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
  have hkey : 4 * s * Δ < w * (3 * B) := by
    rw [hwdef, add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
  -- Chernoff
  set g : Fin Δ → ℝ := fun j => (gcnt rs H d j : ℝ) with hg
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hg0 : ∀ j, 0 ≤ g j := fun j => Nat.cast_nonneg _
  have hgK : ∀ j, g j ≤ k := fun j => by
    simp only [hg]; exact_mod_cast countP_half_le (rs j) H (fun p => d ≤ p.2.1)
  have hcard : (Fintype.card (Fin Δ)) = Δ := Fintype.card_fin Δ
  have hT := card_winA (Δ := Δ) hfit
  have hsumg : ∑ j, g j = B := by simp only [hg, hB, Btot]; push_cast; rfl
  have hch := card_lower_tail_sharp (winA Δ τ0.val w) g hkR hg0 hgK (by rw [hcard]; exact hΔ)
  rw [hT, hsumg, hcard] at hch
  set μ : ℝ := (w : ℝ) * B / Δ with hμ
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hμgt : 4 * (s : ℝ) < 3 * μ := by
    rw [hμ, mul_div_assoc', lt_div_iff₀ hΔR]
    have : ((4 * s * Δ : ℕ) : ℝ) < ((w * (3 * B) : ℕ) : ℝ) := by exact_mod_cast hkey
    push_cast at this; linarith
  have hsub : badA s rs H d τ0 ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      ∑ τ ∈ winA Δ τ0.val w, g (σ τ) ≤ 3 / 4 * μ := by
    intro σ hσ
    simp only [badA, mem_filter, mem_univ, true_and] at hσ ⊢
    have h1 : ∑ τ ∈ winA Δ τ0.val w, g (σ τ) + 1 ≤ s := by
      simp only [hg]; exact_mod_cast hσ.2
    linarith
  have hc1 : ((badA s rs H d τ0).card : ℝ) ≤ Δ.factorial * Real.exp (-(13 * μ) / (400 * k)) :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans hch
  -- `2^λ ≤ exp(13μ / (400 k))`
  have hlamR : 16 * (k : ℝ) * lam ≤ s := by exact_mod_cast hlam
  have h2lam : (2 : ℝ) ^ lam ≤ Real.exp (13 * μ / (400 * k)) := by
    have hlog : Real.log 2 ≤ 6931471808 / 10000000000 := by linarith [Real.log_two_lt_d9]
    calc (2 : ℝ) ^ lam = Real.exp (lam * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
      _ ≤ Real.exp (13 * μ / (400 * k)) := by
          apply Real.exp_le_exp.mpr
          rw [le_div_iff₀ (by positivity)]
          have : (lam : ℝ) * Real.log 2 ≤ 6931471808 / 10000000000 * lam := by
            have := Nat.cast_nonneg (α := ℝ) lam
            nlinarith
          nlinarith
  have hfin : ((badA s rs H d τ0).card : ℝ) * 2 ^ lam ≤ Δ.factorial := by
    calc ((badA s rs H d τ0).card : ℝ) * 2 ^ lam
        ≤ Δ.factorial * Real.exp (-(13 * μ) / (400 * k)) *
            Real.exp (13 * μ / (400 * k)) := by
          gcongr
      _ = Δ.factorial := by
          rw [mul_assoc, ← Real.exp_add]; simp [neg_div]
  exact_mod_cast hfin

theorem card_badB (n : ℕ) (H : RowH k) (d : ℕ) (x : Sq k) (τ0 : Fin Δ) :
    (badB s rs n H d x τ0).card * 2 ^ lamN n ≤ Δ.factorial := by
  set w := wsum s rs H d with hw
  set A := Atot rs H d x with hA
  by_cases hA0 : A = 0
  · have hz : ∀ j, acnt rs H d x j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff.mp (show ∑ j, acnt rs H d x j = 0 from hA0)) j (mem_univ _)
      exact this
    have : badB s rs n H d x τ0 = ∅ := by
      rw [badB, filter_eq_empty_iff]
      intro σ _ h
      simp [hz] at h
    rw [this]; simp
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) τ0.isLt
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hNb : Nb s rs n H d x = 17 * A * (w + 1) / (16 * Δ) + 6 * lamN n := by
    rw [Nb, if_neg hA0]
  set a : Fin Δ → ℕ := fun j => acnt rs H d x j with ha
  have ha1 : ∀ j, a j ≤ 1 := fun j => count_roundIns_le_one (rs j) (H, d, x)
  have hcard : Fintype.card (Fin Δ) = Δ := Fintype.card_fin Δ
  have hch := card_upper_tail_sharp (winB Δ τ0.val w) a ha1 (6 * lamN n) (by rw [hcard]; exact hΔ)
  rw [hcard] at hch
  have hsumA : ∑ i, (a i : ℝ) = A := by simp only [ha, hA, Atot]; push_cast; rfl
  rw [hsumA] at hch
  have hT : ((winB Δ τ0.val w).card : ℝ) ≤ w + 1 := by exact_mod_cast card_winB_le τ0.val w
  have hsub : badB s rs n H d x τ0 ⊆ univ.filter fun σ : Equiv.Perm (Fin Δ) =>
      17 / 16 * ((winB Δ τ0.val w).card * (A : ℝ) / Δ) + ((6 * lamN n : ℕ) : ℝ) ≤
        ((∑ τ ∈ winB Δ τ0.val w, a (σ τ) : ℕ) : ℝ) := by
    intro σ hσ
    simp only [badB, mem_filter, mem_univ, true_and] at hσ ⊢
    rw [hNb] at hσ
    have h1 : ((17 * A * (w + 1) / (16 * Δ) : ℕ) : ℝ) + ((6 * lamN n : ℕ) : ℝ) + 1 ≤
        ((∑ τ ∈ winB Δ τ0.val w, a (σ τ) : ℕ) : ℝ) := by exact_mod_cast hσ
    have h2 := nat_div_add_one_gt (17 * A * (w + 1)) (16 * Δ) (by omega)
    have h3 : 17 / 16 * ((winB Δ τ0.val w).card * (A : ℝ) / Δ) ≤
        ((17 * A * (w + 1) : ℕ) : ℝ) / ((16 * Δ : ℕ) : ℝ) := by
      push_cast
      rw [show (17 : ℝ) / 16 * ((winB Δ τ0.val w).card * (A : ℝ) / Δ) =
        17 * ((winB Δ τ0.val w).card * (A : ℝ)) / (16 * Δ) by field_simp]
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have : (0 : ℝ) ≤ A := Nat.cast_nonneg _
      nlinarith
    linarith
  have h98 : (2 : ℝ) ^ lamN n ≤ (9 / 8) ^ (6 * lamN n) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hfin : ((badB s rs n H d x τ0).card : ℝ) * 2 ^ lamN n ≤ Δ.factorial :=
    (mul_le_mul_of_nonneg_left h98 (Nat.cast_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (by positivity)).trans hch)
  exact_mod_cast hfin

/-- The window properties (A) and (B), for times as natural numbers. -/
structure GoodOrder (n : ℕ) (σ : Equiv.Perm (Fin Δ)) : Prop where
  A : ∀ H d, d < k → ∀ τ0, τ0 + win s rs H d < Δ → s ≤
    ∑ τ ∈ Ioc τ0 (τ0 + win s rs H d),
      (rnd rs σ τ).countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1))
  B : ∀ H d, d < k → ∀ x τ0, τ0 < Δ →
    ∑ τ ∈ Icc τ0 (τ0 + wsum s rs H d), (rnd rs σ τ).countP (fun p => decide (p = (H, d, x))) ≤
      Nb s rs n H d x

theorem goodOrder_of_not_bad (n : ℕ) (σ : Equiv.Perm (Fin Δ))
    (hA : ∀ H (d : Fin k) τ0, σ ∉ badA s rs H d τ0)
    (hB : ∀ H (d : Fin k) x τ0, σ ∉ badB s rs n H d x τ0) : GoodOrder s rs n σ := by
  constructor
  · intro H d hd τ0 hfit
    rw [sum_rnd rs σ _ (fun l => l.countP (fun p => decide (p.1 = H ∧ d ≤ p.2.1))) rfl]
    have := hA H ⟨d, hd⟩ ⟨τ0, by omega⟩
    simp only [badA, mem_filter, mem_univ, true_and, not_and, not_lt] at this
    exact this hfit
  · intro H d hd x τ0 hτ0
    rw [sum_rnd rs σ _ (fun l => l.countP (fun p => decide (p = (H, d, x)))) rfl]
    have := hB H ⟨d, hd⟩ x ⟨τ0, hτ0⟩
    simp only [badB, mem_filter, mem_univ, true_and, not_lt] at this
    exact this

/-- Union bound: some order avoids every bad event. -/
theorem exists_goodOrder (n : ℕ) (hk : 0 < k) (hlam : 16 * k * lamN n ≤ s)
    (hcount : Fintype.card (RowH k × Fin k × Fin Δ) +
      Fintype.card (RowH k × Fin k × Sq k × Fin Δ) < 2 ^ lamN n) :
    ∃ σ, GoodOrder s rs n σ := by
  set Bad : Finset (Equiv.Perm (Fin Δ)) :=
    (univ : Finset (RowH k × Fin k × Fin Δ)).biUnion (fun e => badA s rs e.1 e.2.1 e.2.2) ∪
      (univ : Finset (RowH k × Fin k × Sq k × Fin Δ)).biUnion
        (fun e => badB s rs n e.1 e.2.1 e.2.2.1 e.2.2.2) with hBad
  have hc : Bad.card * 2 ^ lamN n ≤
      (Fintype.card (RowH k × Fin k × Fin Δ) +
        Fintype.card (RowH k × Fin k × Sq k × Fin Δ)) * Δ.factorial := by
    calc Bad.card * 2 ^ lamN n
        ≤ ((∑ e : RowH k × Fin k × Fin Δ, (badA s rs e.1 e.2.1 e.2.2).card) +
          ∑ e : RowH k × Fin k × Sq k × Fin Δ,
            (badB s rs n e.1 e.2.1 e.2.2.1 e.2.2.2).card) * 2 ^ lamN n := by
          apply Nat.mul_le_mul_right
          exact (card_union_le _ _).trans (add_le_add card_biUnion_le card_biUnion_le)
      _ = (∑ e : RowH k × Fin k × Fin Δ, (badA s rs e.1 e.2.1 e.2.2).card * 2 ^ lamN n) +
          ∑ e : RowH k × Fin k × Sq k × Fin Δ,
            (badB s rs n e.1 e.2.1 e.2.2.1 e.2.2.2).card * 2 ^ lamN n := by
          rw [add_mul, sum_mul, sum_mul]
      _ ≤ (∑ _e : RowH k × Fin k × Fin Δ, Δ.factorial) +
          ∑ _e : RowH k × Fin k × Sq k × Fin Δ, Δ.factorial := by
          apply add_le_add
          · exact sum_le_sum fun e _ => card_badA s rs hk hlam _ _ _
          · exact sum_le_sum fun e _ => card_badB s rs n _ _ _ _
      _ = _ := by simp [add_mul]
  have hlt : Bad.card < (univ : Finset (Equiv.Perm (Fin Δ))).card := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    have hf : 0 < Δ.factorial := Nat.factorial_pos Δ
    by_contra hge
    rw [not_lt] at hge
    have := Nat.mul_le_mul hge (le_refl (2 ^ lamN n))
    have h2 := Nat.mul_lt_mul_of_pos_right hcount hf
    rw [mul_comm (2 ^ lamN n)] at h2
    omega
  obtain ⟨σ, -, hσ⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, goodOrder_of_not_bad s rs n σ ?_ ?_⟩
  · intro H d τ0 h
    exact hσ (mem_union_left _ (mem_biUnion.mpr ⟨(H, d, τ0), mem_univ _, h⟩))
  · intro H d x τ0 h
    exact hσ (mem_union_right _ (mem_biUnion.mpr ⟨(H, d, x, τ0), mem_univ _, h⟩))

end SlidingPuzzle.Hub
