import SlidingPuzzle.Hub.InFlightRound

/-! # Summing the in-flight bounds over classes and distances

For a half `H` of length `len` and distance `d`, summing `Nb H d x` over the
classes gives at most `4 len G_d / B_d + 4 G_d / Δ + k λ` (`sum_x_Nb_le`), where
`G_d` counts the insertions from distance `d` and `B_d = Σ_{d' ≥ d} G_{d'}`.
Summing over `d`, `Σ_d G_d / B_d ≤ H(B_0) ≤ 1 + log (kΔ)` (harmonic numbers,
`harmonic_sum_le`), so a half contributes at most
`4 len (1 + log (kΔ)) + 4k + k² λ` (`sum_half_le`). -/
namespace SlidingPuzzle.Hub

open Finset

theorem harmonic_mono' : Monotone (fun n => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]; push_cast
  have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  push_cast at this
  linarith

/-- `a / (a + b) ≤ H(a + b) - H(b)`. -/
theorem div_add_harmonic_le (b : ℕ) : ∀ a : ℕ,
    (a : ℝ) / (a + b) + harmonic b ≤ harmonic (a + b)
  | 0 => by simp
  | a + 1 => by
    have ih := div_add_harmonic_le b a
    rw [show a + 1 + b = (a + b) + 1 by ring, harmonic_succ]
    push_cast
    have h1 : (a : ℝ) / (a + b + 1) ≤ (a : ℝ) / (a + b) := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp
      · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
    have h2 : ((a : ℝ) + 1) / (a + 1 + b) = a / (a + b + 1) + ((a : ℝ) + b + 1)⁻¹ := by
      rw [show (a : ℝ) + 1 + b = a + b + 1 by ring]; field_simp
    rw [h2]; linarith

/-- `Σ_d G_d / B_d ≤ H(B_0)` with `B_d = Σ_{d ≤ d' < K} G_{d'}`. -/
theorem harmonic_sum_le : ∀ (K : ℕ) (G : ℕ → ℕ),
    ∑ d ∈ range K, (G d : ℝ) / ((∑ d' ∈ Ico d K, G d' : ℕ) : ℝ) ≤
      harmonic (∑ d ∈ range K, G d)
  | 0, G => by simp
  | K + 1, G => by
    have ih := harmonic_sum_le K (fun d => G (d + 1))
    rw [sum_range_succ', sum_range_succ']
    have hshift : ∀ d, ∑ d' ∈ Ico (d + 1) (K + 1), G d' = ∑ d' ∈ Ico d K, G (d' + 1) := by
      intro d
      rw [← sum_Ico_add' (f := G) (a := d) (b := K) (c := 1)]
    simp_rw [hshift]
    have h0 : ∑ d' ∈ Ico 0 (K + 1), G d' = G 0 + ∑ d ∈ range K, G (d + 1) := by
      rw [← range_eq_Ico, sum_range_succ', add_comm]
    rw [h0, add_comm (∑ d ∈ range K, G (d + 1)) (G 0)]
    have hk := div_add_harmonic_le (∑ d ∈ range K, G (d + 1)) (G 0)
    push_cast at hk ih ⊢
    linarith

section params

variable {k Δ : ℕ} (s : ℕ) (rs : Fin Δ → Round k)

/-- `G_d`: all insertions into `H` from distance `d`. -/
noncomputable def Gtot (H : RowH k) (d : ℕ) : ℕ := ∑ j, gdist rs H d j

theorem Btot_eq_sum (H : RowH k) (d : ℕ) : Btot rs H d = ∑ d' ∈ Ico d k, Gtot rs H d' := by
  unfold Btot Gtot gcnt gdist
  simp_rw [countP_ge_eq_sum]
  exact sum_comm

theorem Gtot_le_Btot (H : RowH k) (d : ℕ) : Gtot rs H d ≤ Btot rs H d := by
  unfold Btot Gtot gcnt gdist
  apply sum_le_sum; intro j _
  apply List.countP_mono_left
  intro p _ hp
  simp only [decide_eq_true_eq] at hp ⊢
  exact ⟨hp.1, hp.2.ge⟩

theorem Btot_le (H : RowH k) (d : ℕ) : Btot rs H d ≤ k * Δ := by
  unfold Btot
  calc ∑ j, gcnt rs H d j ≤ ∑ _j : Fin Δ, k := sum_le_sum fun j _ =>
        countP_half_le (rs j) H (fun p => d ≤ p.2.1)
    _ = k * Δ := by simp [mul_comm]

theorem sum_Atot (H : RowH k) (d : ℕ) : ∑ x, Atot rs H d x = Gtot rs H d := by
  unfold Atot Gtot acnt gdist
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_count_class (rs j) H d

theorem card_Atot_ne_zero (H : RowH k) (d : ℕ) :
    (univ.filter fun x => Atot rs H d x ≠ 0).card ≤ k := by
  calc _ ≤ (univ : Finset (Fin k)).card := by
        apply card_le_card_of_injOn (fun x => x.1) (fun _ _ => mem_coe.mpr (mem_univ _))
        have hcol : ∀ x, Atot rs H d x ≠ 0 → x.2 = H.2.1 := by
          intro x hx
          obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero hx
          obtain ⟨p, hp, hpx⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hj)
          simp only [decide_eq_true_eq] at hpx
          have := class_col_of_mem hp
          rw [hpx] at this
          exact this
        intro a ha b hb hab
        simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ha hb
        exact Prod.ext hab ((hcol a ha).trans (hcol b hb).symm)
    _ = k := by simp

theorem sum_x_Nb_le (hs : 1 ≤ s) (n : ℕ) (H : RowH k) (d : ℕ) :
    ∑ x, (Nb s rs n H d x : ℝ) ≤ 17 / 15 * rowLen k s H * ((Gtot rs H d : ℝ) / Btot rs H d) +
      17 / 8 * (Gtot rs H d : ℝ) / Δ + k * (6 * lamN n) := by
  set w := win s rs H d with hw
  set G := Gtot rs H d with hG
  set B := Btot rs H d with hB
  have h1 : ∀ x, (Nb s rs n H d x : ℝ) ≤ 17 * (Atot rs H d x : ℝ) * (w + 1) / (16 * Δ) +
      (if Atot rs H d x ≠ 0 then ((6 * lamN n : ℕ) : ℝ) else 0) := by
    intro x
    unfold Nb
    by_cases h : Atot rs H d x = 0
    · rw [if_pos h, if_neg (not_not.mpr h)]; simp only [Nat.cast_zero, add_zero]; positivity
    · rw [if_neg h, if_pos h]
      have := Nat.cast_div_le (α := ℝ) (m := 17 * Atot rs H d x * (w + 1)) (n := 16 * Δ)
      push_cast at this ⊢
      linarith
  have h2 : ∑ x : Sq k, (if Atot rs H d x ≠ 0 then ((6 * lamN n : ℕ) : ℝ) else 0) ≤
      k * ((6 * lamN n : ℕ) : ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast card_Atot_ne_zero rs H d
  have h3 : ∑ x, 17 * (Atot rs H d x : ℝ) * (w + 1) / (16 * Δ) = 17 * (G : ℝ) * (w + 1) / (16 * Δ) := by
    rw [← sum_div, ← sum_mul, ← mul_sum]
    congr 3
    rw [hG, ← sum_Atot]; push_cast; rfl
  have h5 : 17 * (G : ℝ) * (w + 1) / (16 * Δ) ≤
      17 / 15 * rowLen k s H * ((G : ℝ) / B) + 17 / 8 * (G : ℝ) / Δ := by
    by_cases hG0 : G = 0
    · rw [hG0]; simp
    obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero hG0
    have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    obtain ⟨p, hp, hpH⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hj)
    simp only [decide_eq_true_eq] at hpH
    have hlen := insPos_lt_rowLen_of_mem hs hp
    rw [hpH.1, hpH.2] at hlen
    have hGB : G ≤ B := Gtot_le_Btot rs H d
    have hB0 : B ≠ 0 := by omega
    have hwle : w ≤ 16 * (insPos k s H d + 1) * Δ / (15 * B) + 1 := by
      rw [hw, win, if_neg hB0]; exact min_le_right _ _
    have hBR : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB0
    have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
    have hwR : (w : ℝ) ≤ 16 * (rowLen k s H : ℝ) * Δ / (15 * B) + 1 := by
      have e1 : (w : ℝ) ≤ ((16 * (insPos k s H d + 1) * Δ / (15 * B) : ℕ) : ℝ) + 1 := by
        exact_mod_cast hwle
      have e2 := Nat.cast_div_le (α := ℝ) (m := 16 * (insPos k s H d + 1) * Δ) (n := 15 * B)
      have e3 : ((16 * (insPos k s H d + 1) * Δ : ℕ) : ℝ) ≤ 16 * (rowLen k s H : ℝ) * Δ := by
        push_cast
        have : ((insPos k s H d : ℕ) : ℝ) + 1 ≤ rowLen k s H := by exact_mod_cast hlen
        nlinarith
      have e4 : ((16 * (insPos k s H d + 1) * Δ : ℕ) : ℝ) / ((15 * B : ℕ) : ℝ) ≤
          16 * (rowLen k s H : ℝ) * Δ / (15 * B) := by
        push_cast
        exact div_le_div_of_nonneg_right (by exact_mod_cast e3) (by positivity)
      linarith
    have hGR : (0 : ℝ) ≤ G := Nat.cast_nonneg _
    calc 17 * (G : ℝ) * (w + 1) / (16 * Δ) ≤
          17 * (G : ℝ) * (16 * (rowLen k s H : ℝ) * Δ / (15 * B) + 2) / (16 * Δ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 17 / 15 * rowLen k s H * ((G : ℝ) / B) + 17 / 8 * (G : ℝ) / Δ := by
          field_simp; ring
  calc ∑ x, (Nb s rs n H d x : ℝ)
      ≤ ∑ x, (17 * (Atot rs H d x : ℝ) * (w + 1) / (16 * Δ) +
          (if Atot rs H d x ≠ 0 then ((6 * lamN n : ℕ) : ℝ) else 0)) := sum_le_sum fun x _ => h1 x
    _ ≤ _ := by rw [sum_add_distrib, h3]; push_cast at h2 ⊢; linarith

theorem sum_half_le (hs : 1 ≤ s) (n : ℕ) (H : RowH k) :
    ∑ d ∈ range k, ∑ x, (Nb s rs n H d x : ℝ) ≤
      17 / 15 * rowLen k s H * (1 + Real.log (k * Δ)) + 17 / 8 * k + k * k * (6 * lamN n) := by
  have hsum := sum_le_sum fun d (_ : d ∈ range k) => sum_x_Nb_le s rs hs n H d
  refine hsum.trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hB0 : Btot rs H 0 = ∑ d ∈ range k, Gtot rs H d := by
    rw [Btot_eq_sum, range_eq_Ico]
  have hharm : ∑ d ∈ range k, (Gtot rs H d : ℝ) / Btot rs H d ≤ 1 + Real.log (k * Δ) := by
    have := harmonic_sum_le k (Gtot rs H)
    simp_rw [← Btot_eq_sum] at this
    rw [← hB0] at this
    refine this.trans ((harmonic_mono' (Btot_le rs H 0)).trans ?_)
    have := harmonic_le_one_add_log (k * Δ)
    push_cast at this; exact this
  have hG : ∑ d ∈ range k, 17 / 8 * (Gtot rs H d : ℝ) / Δ ≤ 17 / 8 * k := by
    rw [← sum_div, ← mul_sum]
    have : (∑ d ∈ range k, (Gtot rs H d : ℝ)) ≤ k * Δ := by
      have := Btot_le rs H 0
      rw [hB0] at this; exact_mod_cast this
    rcases Nat.eq_zero_or_pos Δ with h | h
    · subst h; simp
    · have hΔR : (0 : ℝ) < Δ := by exact_mod_cast h
      rw [div_le_iff₀ hΔR]; nlinarith
  have hlen : (0 : ℝ) ≤ 17 / 15 * rowLen k s H := by positivity
  have := mul_le_mul_of_nonneg_left hharm hlen
  nlinarith

end params

end SlidingPuzzle.Hub
