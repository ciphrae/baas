import SlidingPuzzle.Hub.InFlightRound

/-! # Summing the in-flight bounds over classes and distances

For a half `H` and distance `d`, summing `Nb H d x` over the classes gives at
most `(17/16) G_d (W_d + 1)/Δ + k·6λ` (`sum_x_Nb_le`), where `G_d` counts the
insertions from distance `d` and `W_d = ∑_{j ≤ d} w_j` is the segmented
residence window. Since `w_j ≤ 4sΔ/(3B_j) + 1` with `B_j = ∑_{d' ≥ j} G_{d'}`,
the rate-weighted windows telescope: `∑_d G_d ∑_{j ≤ d} 1/B_j` counts the
bands `j` with `B_j ≠ 0` (`sum_mul_sum_inv_le`), and these bands lie in the
half (`card_bands_mul_le`). A half therefore contributes at most
`(17/12)(len + k) + (17/16)k(k+1) + 6k²λ` (`sum_half_le`), with no logarithm. -/
namespace SlidingPuzzle.Hub

open Finset

/-- The rate-weighted windows telescope: `∑_d G_d ∑_{j ≤ d} 1/B_j` is the number
of nonzero tails `B_j = ∑_{j ≤ d' < K} G_{d'}`. -/
theorem sum_mul_sum_inv_le (K : ℕ) (G : ℕ → ℕ) :
    ∑ d ∈ range K, (G d : ℝ) * ∑ j ∈ range (d + 1), ((∑ d' ∈ Ico j K, G d' : ℕ) : ℝ)⁻¹ ≤
      ((range K).filter fun j => ∑ d' ∈ Ico j K, G d' ≠ 0).card := by
  have h1 : ∑ d ∈ range K, (G d : ℝ) * ∑ j ∈ range (d + 1), ((∑ d' ∈ Ico j K, G d' : ℕ) : ℝ)⁻¹ =
      ∑ j ∈ range K, ((∑ d' ∈ Ico j K, G d' : ℕ) : ℝ) *
        ((∑ d' ∈ Ico j K, G d' : ℕ) : ℝ)⁻¹ := by
    simp_rw [mul_sum]
    rw [range_eq_Ico]
    simp_rw [range_eq_Ico]
    rw [← sum_Ico_Ico_comm 0 K (fun j d => (G d : ℝ) * ((∑ d' ∈ Ico j K, G d' : ℕ) : ℝ)⁻¹)]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_mul]; push_cast; rfl
  rw [h1, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun j _ => ?_
  split_ifs with h
  · have : ((∑ d' ∈ Ico j K, G d' : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h
    rw [mul_inv_cancel₀ this]; simp
  · push Not at h; rw [h]; simp

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

/-- Bands with insertions from distances `≥ j` lie in the half. -/
theorem card_bands_mul_le (hks : k + 1 ≤ s) (H : RowH k) :
    ((range k).filter fun j => Btot rs H j ≠ 0).card * s ≤ rowLen k s H + k := by
  have hsub : (range k).filter (fun j => Btot rs H j ≠ 0) ⊆ range ((rowLen k s H + k) / s) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hj.2
    obtain ⟨p, hp, hpH⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hi)
    simp only [decide_eq_true_eq] at hpH
    have hlen := insPos_lt_rowLen_of_mem (by omega : 1 ≤ s) hp
    rw [hpH.1] at hlen
    have hmono := insPos_mono s H hpH.2
    have hpos : (j + 1) * s ≤ insPos k s H j + 1 + k := by
      have : k + 1 ≤ (j + 1) * s := le_trans hks (Nat.le_mul_of_pos_left s (by omega))
      unfold insPos; split <;> omega
    rw [Nat.lt_div_iff_mul_lt (by omega)]
    rw [add_mul, one_mul] at hpos
    omega
  have := card_le_card hsub
  rw [card_range] at this
  exact (Nat.mul_le_mul_right s this).trans (Nat.div_mul_le_self _ _)

theorem sum_x_Nb_le (n : ℕ) (H : RowH k) (d : ℕ) :
    ∑ x, (Nb s rs n H d x : ℝ) ≤ 17 * (Gtot rs H d : ℝ) * (wsum s rs H d + 1) / (16 * Δ) +
      k * (6 * lamN n) := by
  set w := wsum s rs H d with hw
  set G := Gtot rs H d with hG
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
  have h3 : ∑ x, 17 * (Atot rs H d x : ℝ) * (w + 1) / (16 * Δ) =
      17 * (G : ℝ) * (w + 1) / (16 * Δ) := by
    rw [← sum_div, ← sum_mul, ← mul_sum]
    congr 3
    rw [hG, ← sum_Atot]; push_cast; rfl
  calc ∑ x, (Nb s rs n H d x : ℝ)
      ≤ ∑ x, (17 * (Atot rs H d x : ℝ) * (w + 1) / (16 * Δ) +
          (if Atot rs H d x ≠ 0 then ((6 * lamN n : ℕ) : ℝ) else 0)) := sum_le_sum fun x _ => h1 x
    _ ≤ _ := by rw [sum_add_distrib, h3]; push_cast at h2 ⊢; linarith

/-- The residence window against the tail rates: `G_d (W_d + 1) ≤
(4sΔ/3) G_d ∑_{j ≤ d} 1/B_j + (d + 2) G_d`. -/
theorem Gtot_mul_wsum_le (H : RowH k) (d : ℕ) :
    (Gtot rs H d : ℝ) * (wsum s rs H d + 1) ≤
      4 * s * Δ / 3 * ((Gtot rs H d : ℝ) *
        ∑ j ∈ range (d + 1), ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹) +
      (d + 2) * (Gtot rs H d : ℝ) := by
  by_cases hG0 : Gtot rs H d = 0
  · rw [hG0]; simp
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hG0
  obtain ⟨p, hp, hpH⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hi)
  simp only [decide_eq_true_eq] at hpH
  have hdk : d < k := hpH.2 ▸ dist_lt_of_mem hp
  have hΔ : 0 < Δ := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hGR : (0 : ℝ) ≤ Gtot rs H d := Nat.cast_nonneg _
  -- every band `j ≤ d` has positive tail rate
  have hwin : ∀ j ∈ range (d + 1), (win s rs H j : ℝ) ≤
      4 * s * Δ / 3 * ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹ + 1 := by
    intro j hj
    have hjd := mem_range.mp hj
    have hGB : Gtot rs H d ≤ Btot rs H j := by
      rw [Btot_eq_sum]
      exact single_le_sum (f := Gtot rs H) (fun _ _ => Nat.zero_le _)
        (mem_Ico.mpr ⟨by omega, hdk⟩)
    have hB0 : Btot rs H j ≠ 0 := by omega
    have hBR : (0 : ℝ) < Btot rs H j := by exact_mod_cast Nat.pos_of_ne_zero hB0
    have hle : win s rs H j ≤ 4 * s * Δ / (3 * Btot rs H j) + 1 := by
      rw [win, if_neg hB0]; exact min_le_right _ _
    have e2 := Nat.cast_div_le (α := ℝ) (m := 4 * s * Δ) (n := 3 * Btot rs H j)
    rw [← Btot_eq_sum]
    have : (win s rs H j : ℝ) ≤ ((4 * s * Δ / (3 * Btot rs H j) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hle
    have e3 : ((4 * s * Δ : ℕ) : ℝ) / ((3 * Btot rs H j : ℕ) : ℝ) =
        4 * s * Δ / 3 * ((Btot rs H j : ℕ) : ℝ)⁻¹ := by
      push_cast; field_simp
    linarith
  have hsum : (wsum s rs H d : ℝ) ≤ 4 * s * Δ / 3 *
      ∑ j ∈ range (d + 1), ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹ + (d + 1) := by
    unfold wsum
    push_cast
    calc ∑ j ∈ range (d + 1), (win s rs H j : ℝ)
        ≤ ∑ j ∈ range (d + 1), (4 * s * Δ / 3 * ((∑ d' ∈ Ico j k, Gtot rs H d' : ℕ) : ℝ)⁻¹ + 1) :=
          sum_le_sum hwin
      _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp
  have := mul_le_mul_of_nonneg_left (add_le_add_right hsum 1) hGR
  nlinarith

theorem sum_half_le (hks : k + 1 ≤ s) (n : ℕ) (H : RowH k) :
    ∑ d ∈ range k, ∑ x, (Nb s rs n H d x : ℝ) ≤
      17 / 12 * (rowLen k s H + k) + 17 / 16 * (k * (k + 1)) + k * k * (6 * lamN n) := by
  have hsum := sum_le_sum fun d (_ : d ∈ range k) => sum_x_Nb_le s rs n H d
  refine hsum.trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos Δ with hΔ0 | hΔ
  · subst hΔ0
    simp only [Nat.cast_zero, mul_zero, div_zero, sum_const_zero, zero_add]
    have : (0 : ℝ) ≤ 17 / 12 * (rowLen k s H + k) + 17 / 16 * (k * (k + 1)) := by positivity
    nlinarith
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  -- the telescoping sum
  have htel := sum_mul_sum_inv_le k (Gtot rs H)
  have hband := card_bands_mul_le s rs hks H
  simp_rw [← Btot_eq_sum] at htel
  have hbandR : ((((range k).filter fun j => Btot rs H j ≠ 0).card : ℕ) : ℝ) * s ≤
      rowLen k s H + k := by exact_mod_cast hband
  have hGsum : ∑ d ∈ range k, (Gtot rs H d : ℝ) ≤ k * Δ := by
    have := Btot_le rs H 0
    rw [Btot_eq_sum, ← range_eq_Ico] at this; exact_mod_cast this
  have hterm : ∀ d ∈ range k, 17 * (Gtot rs H d : ℝ) * (wsum s rs H d + 1) / (16 * Δ) ≤
      17 / 16 * (4 * s / 3 * ((Gtot rs H d : ℝ) *
        ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹)) +
      17 / 16 * ((k + 1) * (Gtot rs H d : ℝ) / Δ) := by
    intro d hd
    have hdk := mem_range.mp hd
    have h := Gtot_mul_wsum_le s rs H d
    simp_rw [← Btot_eq_sum] at h
    have hGR : (0 : ℝ) ≤ Gtot rs H d := Nat.cast_nonneg _
    have hd2 : ((d : ℝ) + 2) * (Gtot rs H d : ℝ) ≤ ((k : ℝ) + 1) * (Gtot rs H d) := by
      have : (d : ℝ) + 2 ≤ k + 1 := by
        have : (d : ℝ) + 1 ≤ k := by exact_mod_cast hdk
        linarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : (17 / 16 * (4 * (s : ℝ) / 3 * ((Gtot rs H d : ℝ) *
        ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹)) +
        17 / 16 * ((k + 1) * (Gtot rs H d : ℝ) / Δ)) * (16 * Δ) =
        17 * (4 * s * Δ / 3 * ((Gtot rs H d : ℝ) *
          ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹) + ((k : ℝ) + 1) * Gtot rs H d) := by
      field_simp
    rw [e]
    nlinarith
  refine (add_le_add (sum_le_sum hterm) le_rfl).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have h1 : 4 * (s : ℝ) / 3 * ∑ d ∈ range k, ((Gtot rs H d : ℝ) *
      ∑ j ∈ range (d + 1), ((Btot rs H j : ℕ) : ℝ)⁻¹) ≤ 4 / 3 * (rowLen k s H + k) := by
    have := mul_le_mul_of_nonneg_left htel (show (0 : ℝ) ≤ 4 * s / 3 by positivity)
    nlinarith
  have h2 : ∑ d ∈ range k, ((k : ℝ) + 1) * (Gtot rs H d : ℝ) / Δ ≤ k * (k + 1) := by
    rw [← sum_div, ← mul_sum, div_le_iff₀ hΔR]
    have : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith
  nlinarith

end params

end SlidingPuzzle.Hub
