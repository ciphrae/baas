import SlidingPuzzle.Port.Grid16
import SlidingPuzzle.Port.LogLog
import SlidingPuzzle.Port.AsympDeep

/-! # Uniform constants from `2²³`

On the grid of free level `≥ 16` (`port_coef16`) the error coefficient is
`c = 1 + 8 √λ (1 + 2/d) (172 + 53 q/λ) + 240.96 (m + 1)`. For `⌊log₂ n⌋ ≤ 60` it is
bounded case by case (convex in `d`, so the two ends of the range of `d` suffice), beyond
by `c ≤ 3743.3 √L + 86.92 L + 9630/√L`, `L = ln n`. This gives
`OPT(B) ≤ M(B) + 940 n^(5/2) ln n` and, with `port_optimalLength_le` for
`4.2 ≤ ln ln n ≤ 42` and `port_loglog` beyond, `OPT(B) ≤ M(B) + 2700 n^(5/2) ln n / ln ln n`. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- `(1 + 2/d)(A + B d)` is convex in `d`: bounded by its values at the ends. -/
theorem conv_d {A B d D U V : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 < D) (hDd : D ≤ d)
    (hdU : d ≤ U) (h1 : (1 + 2 / D) * (A + B * D) ≤ V) (h2 : (1 + 2 / U) * (A + B * U) ≤ V) :
    (1 + 2 / d) * (A + B * d) ≤ V := by
  have hd : 0 < d := by linarith
  have hU : 0 < U := by linarith
  rcases eq_or_lt_of_le (le_trans hDd hdU) with hDU | hDU
  · have : d = D := le_antisymm (hDU ▸ hdU) hDd
    rw [this]; exact h1
  -- `1/d ≤ 1/D + 1/U - d/(D U)`
  have hinv : 1 / d ≤ 1 / D + 1 / U - d / (D * U) := by
    have hp : 0 ≤ (d - D) * (U - d) := mul_nonneg (by linarith) (by linarith)
    rw [div_add_div _ _ hD.ne' hU.ne', div_sub_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ hd (by positivity)]
    nlinarith [mul_pos hD hU, mul_pos (mul_pos hD hU) hd]
  have e : ∀ x : ℝ, 0 < x → (1 + 2 / x) * (A + B * x) = A + 2 * B + B * x + 2 * A * (1 / x) := by
    intro x hx; field_simp; ring
  rw [e d hd]
  rw [e D hD] at h1; rw [e U hU] at h2
  -- a linear function of `d` below `V` at both ends
  set ℓ : ℝ → ℝ := fun x => A + 2 * B + B * x + 2 * A * (1 / D + 1 / U - x / (D * U)) with hℓ
  have hℓD : ℓ D = A + 2 * B + B * D + 2 * A * (1 / D) := by
    simp only [hℓ]; field_simp; ring
  have hℓU : ℓ U = A + 2 * B + B * U + 2 * A * (1 / U) := by
    simp only [hℓ]; field_simp; ring
  have hle : A + 2 * B + B * d + 2 * A * (1 / d) ≤ ℓ d := by
    simp only [hℓ]; nlinarith
  have hlin : ℓ d = ((U - d) * ℓ D + (d - D) * ℓ U) / (U - D) := by
    simp only [hℓ]; field_simp; ring
  have hUD : 0 < U - D := by linarith
  have : ℓ d ≤ V := by
    rw [hlin, div_le_iff₀ hUD]
    have a1 := mul_le_mul_of_nonneg_left (hℓD ▸ h1) (show 0 ≤ U - d by linarith)
    have a2 := mul_le_mul_of_nonneg_left (hℓU ▸ h2) (show 0 ≤ d - D by linarith)
    nlinarith
  linarith

/-- The coefficient against numeric bounds for `√λ`, `m`, the range of `d`. -/
theorem coef16_num {lam q m d mb U : ℕ} {a V : ℝ} (hlam : 0 < lam) (ha0 : 0 ≤ a)
    (ha : (lam : ℝ) ≤ a ^ 2) (hm : m ≤ mb) (hd : 16 ≤ d) (hdU : d ≤ U) (hq : q ≤ 6 * m + d)
    (hV1 : (1 + 2 / (16 : ℝ)) * ((172 + 53 * (6 * (mb : ℝ)) / lam) + 53 / lam * 16) ≤ V)
    (hV2 : (1 + 2 / (U : ℝ)) * ((172 + 53 * (6 * (mb : ℝ)) / lam) + 53 / lam * U) ≤ V) :
    1 + 8 * Real.sqrt lam * (1 + 2 / (d : ℝ)) * (172 + 53 * (q : ℝ) / lam) +
      240.96 * ((m : ℝ) + 1) ≤ 1 + 8 * a * V + 240.96 * ((mb : ℝ) + 1) := by
  have hl0 : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hsa : Real.sqrt lam ≤ a := by
    rw [show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha0).symm]; exact Real.sqrt_le_sqrt ha
  have hmm : (m : ℝ) ≤ mb := by exact_mod_cast hm
  have hqq : (q : ℝ) ≤ 6 * mb + d := by
    have : (q : ℝ) ≤ 6 * m + d := by exact_mod_cast hq
    linarith
  have hdR : (16 : ℝ) ≤ d := by exact_mod_cast hd
  have hUR : (d : ℝ) ≤ U := by exact_mod_cast hdU
  have hlane : 172 + 53 * (q : ℝ) / lam ≤ (172 + 53 * (6 * (mb : ℝ)) / lam) + 53 / lam * d := by
    have : 53 * (q : ℝ) / lam ≤ 53 * (6 * (mb : ℝ) + d) / lam :=
      div_le_div_of_nonneg_right (by linarith) hl0.le
    have e : 53 * (6 * (mb : ℝ) + d) / lam = 53 * (6 * (mb : ℝ)) / lam + 53 / lam * d := by ring
    linarith
  have hconv := conv_d (A := 172 + 53 * (6 * (mb : ℝ)) / lam) (B := 53 / lam) (d := d) (D := 16)
    (U := U) (V := V) (by positivity) (by positivity) (by norm_num) hdR hUR hV1 hV2
  have hρ0 : 0 ≤ 1 + 2 / (d : ℝ) := by positivity
  have h1 : (1 + 2 / (d : ℝ)) * (172 + 53 * (q : ℝ) / lam) ≤ V :=
    le_trans (mul_le_mul_of_nonneg_left hlane hρ0) hconv
  have h0 : 0 ≤ (1 + 2 / (d : ℝ)) * (172 + 53 * (q : ℝ) / lam) := by positivity
  have h2 : 8 * Real.sqrt lam * ((1 + 2 / (d : ℝ)) * (172 + 53 * (q : ℝ) / lam)) ≤ 8 * a * V :=
    mul_le_mul (by linarith) h1 h0 (by positivity)
  have e : 8 * Real.sqrt lam * (1 + 2 / (d : ℝ)) * (172 + 53 * (q : ℝ) / lam) =
      8 * Real.sqrt lam * ((1 + 2 / (d : ℝ)) * (172 + 53 * (q : ℝ) / lam)) := by ring
  rw [e]
  linarith

/-- Seven terms of the exponential series. -/
theorem exp_ge_taylor {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 ≤ Real.exp x := by
  have := Real.sum_le_exp_of_nonneg hx 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

/-- `ln L ≤ k + x` from a lower bound of `e^(k + x)`. -/
theorem log_le_of {L Lh x : ℝ} (k : ℕ) (hx : 0 ≤ x) (hL0 : 0 < L) (hL : L ≤ Lh)
    (h : Lh ≤ 2.7182818283 ^ k *
      (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720)) :
    Real.log L ≤ k + x := by
  rw [Real.log_le_iff_le_exp hL0, Real.exp_add]
  have h1 : (2.7182818283 : ℝ) ^ k ≤ Real.exp k := by
    rw [← Real.exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k
  have h2 := exp_ge_taylor hx
  have := mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
  linarith

/-- The numeric conclusion of a case. -/
theorem fin16 {c L K Lb Lh : ℝ} (k : ℕ) {x : ℝ} (hc : c ≤ K) (hc0 : 0 ≤ c) (hLb : Lb ≤ L)
    (hLh : L ≤ Lh) (hx : 0 ≤ x)
    (hexp : Lh ≤ 2.7182818283 ^ k *
      (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720))
    (hLb0 : 0 < Lb) (hK1 : K ≤ 940 * Lb) (hK2 : K * (k + x) ≤ 2700 * Lb) :
    c ≤ 940 * L ∧ c * Real.log L ≤ 2700 * L := by
  have hL0 : 0 < L := by linarith
  have ht := log_le_of k hx hL0 hLh hexp
  refine ⟨by linarith, ?_⟩
  have hk0 : (0 : ℝ) ≤ k + x := by positivity
  have h1 : c * Real.log L ≤ c * (k + x) := mul_le_mul_of_nonneg_left ht hc0
  have h2 : c * (k + x) ≤ K * (k + x) := mul_le_mul_of_nonneg_right hc hk0
  linarith

set_option maxHeartbeats 4000000 in
/-- The coefficient for `⌊log₂ n⌋ ≤ 60`, case by case. -/
theorem coef16_small {n m d q : ℕ} (hn : 2 ^ 23 ≤ n) (hE60 : Nat.log 2 n ≤ 60) (hm1 : 1 ≤ m)
    (hPm : 16 * GroupedOrder.lamN n * (16 * 4 ^ m) ^ 2 ≤ n)
    (h4d : 16 * GroupedOrder.lamN n * (4 ^ m * d) ^ 2 ≤ n) (hd16 : 16 ≤ d)
    (hdj : d < 24 ∨ 6 ^ m * d < 64 * 4 ^ m) (hq : q ≤ 6 * m + d) :
    1 + 8 * Real.sqrt (GroupedOrder.lamN n) * (1 + 2 / (d : ℝ)) *
      (172 + 53 * (q : ℝ) / (GroupedOrder.lamN n)) + 240.96 * ((m : ℝ) + 1) ≤ 940 * Real.log n ∧
    (1 + 8 * Real.sqrt (GroupedOrder.lamN n) * (1 + 2 / (d : ℝ)) *
      (172 + 53 * (q : ℝ) / (GroupedOrder.lamN n)) + 240.96 * ((m : ℝ) + 1)) *
      Real.log (Real.log n) ≤ 2700 * Real.log n := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hge : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hE23 : 23 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hlam : GroupedOrder.lamN n = 3 * (Nat.log 2 n + 1) := rfl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLE : (Nat.log 2 n : ℝ) * 0.6931471803 ≤ Real.log n := by
    have c' : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    push_cast at c'
    have := Real.log_le_log (by positivity) c'
    rw [Real.log_pow] at this
    have := Real.log_two_gt_d9
    have hE0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
    nlinarith
  have hLU : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * 0.6931471808 := by
    have c' : (n : ℝ) ≤ ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
    push_cast at c'
    have h1 := Real.log_le_log hn0 c'
    rw [Real.log_pow] at h1
    have h2 := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le
      (show (0 : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) by positivity)
    push_cast at h1 h2 ⊢
    linarith
  generalize Nat.log 2 n = E at hlt hge hE23 hE60 hLE hLU hlam
  rw [hlam] at hPm h4d ⊢
  interval_cases E
  · -- `⌊log₂ n⌋ = 23`
    rw [show 3 * (23 + 1) = 72 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 1 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 30 := d_le_of h4d hlt hm1 (by norm_num)
    have hc := coef16_num (lam := 72) (a := 8.4853) (V := 211.734) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 2 (x := 0.812) (K := 14856.0) (Lb := 15.94238) (Lh := 24 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 24`
    rw [show 3 * (24 + 1) = 75 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 1 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 41 := d_le_of h4d hlt hm1 (by norm_num)
    have hc := coef16_num (lam := 75) (a := 8.6603) (V := 215.224) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 2 (x := 0.853) (K := 15394.2) (Lb := 16.63553) (Lh := 25 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 25`
    rw [show 3 * (25 + 1) = 78 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 1 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 78) (a := 8.8318) (V := 214.359) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 2 (x := 0.892) (K := 15628.4) (Lb := 17.32867) (Lh := 26 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 26`
    rw [show 3 * (26 + 1) = 81 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 81) (a := 9.0) (V := 217.207) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 2 (x := 0.93) (K := 16362.8) (Lb := 18.02182) (Lh := 27 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 27`
    rw [show 3 * (27 + 1) = 84 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 84) (a := 9.1652) (V := 215.885) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 2 (x := 0.966) (K := 16553.0) (Lb := 18.71497) (Lh := 28 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 28`
    rw [show 3 * (28 + 1) = 87 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 87) (a := 9.3274) (V := 214.654) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.001) (K := 16741.2) (Lb := 19.40812) (Lh := 29 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 29`
    rw [show 3 * (29 + 1) = 90 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 2 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 90) (a := 9.4869) (V := 213.505) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.035) (K := 16927.9) (Lb := 20.10126) (Lh := 30 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 30`
    rw [show 3 * (30 + 1) = 93 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 3 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 93) (a := 9.6437) (V := 216.013) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.068) (K := 17630.2) (Lb := 20.79441) (Lh := 31 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 31`
    rw [show 3 * (31 + 1) = 96 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 3 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 96) (a := 9.798) (V := 214.893) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.1) (K := 17809.1) (Lb := 21.48756) (Lh := 32 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 32`
    rw [show 3 * (32 + 1) = 99 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 3 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 99) (a := 9.9499) (V := 213.978) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.13) (K := 17997.4) (Lb := 22.1807) (Lh := 33 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 33`
    rw [show 3 * (33 + 1) = 102 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 3 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 102) (a := 10.0996) (V := 213.375) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.16) (K := 18204.9) (Lb := 22.87385) (Lh := 34 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 34`
    rw [show 3 * (34 + 1) = 105 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 4 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 105) (a := 10.247) (V := 216.215) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.189) (K := 18930.3) (Lb := 23.567) (Lh := 35 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 35`
    rw [show 3 * (35 + 1) = 108 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 4 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 108) (a := 10.3924) (V := 215.584) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.218) (K := 19129.3) (Lb := 24.26015) (Lh := 36 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 36`
    rw [show 3 * (36 + 1) = 111 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 4 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 111) (a := 10.5357) (V := 214.987) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.245) (K := 19326.2) (Lb := 24.95329) (Lh := 37 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 37`
    rw [show 3 * (37 + 1) = 114 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 4 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 114) (a := 10.6771) (V := 214.422) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.272) (K := 19521.1) (Lb := 25.64644) (Lh := 38 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 38`
    rw [show 3 * (38 + 1) = 117 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 5 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 117) (a := 10.8167) (V := 216.943) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.298) (K := 20219.7) (Lb := 26.33959) (Lh := 39 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 39`
    rw [show 3 * (39 + 1) = 120 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 5 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 120) (a := 10.9545) (V := 216.357) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.323) (K := 20407.5) (Lb := 27.03274) (Lh := 40 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 40`
    rw [show 3 * (40 + 1) = 123 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 5 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 123) (a := 11.0906) (V := 215.799) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.348) (K := 20593.5) (Lb := 27.72588) (Lh := 41 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 41`
    rw [show 3 * (41 + 1) = 126 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 5 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 126) (a := 11.225) (V := 215.268) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.372) (K := 20777.9) (Lb := 28.41903) (Lh := 42 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 42`
    rw [show 3 * (42 + 1) = 129 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 5 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 129) (a := 11.3579) (V := 214.762) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.395) (K := 20960.8) (Lb := 29.11218) (Lh := 43 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 43`
    rw [show 3 * (43 + 1) = 132 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 6 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 132) (a := 11.4892) (V := 216.989) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.418) (K := 21632.0) (Lb := 29.80532) (Lh := 44 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 44`
    rw [show 3 * (44 + 1) = 135 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 6 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 135) (a := 11.619) (V := 216.467) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.441) (K := 21808.8) (Lb := 30.49847) (Lh := 45 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 45`
    rw [show 3 * (45 + 1) = 138 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 6 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 138) (a := 11.7474) (V := 215.968) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.463) (K := 21984.3) (Lb := 31.19162) (Lh := 46 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 46`
    rw [show 3 * (46 + 1) = 141 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 6 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 141) (a := 11.8744) (V := 215.49) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.484) (K := 22158.3) (Lb := 31.88477) (Lh := 47 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 47`
    rw [show 3 * (47 + 1) = 144 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 7 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 144) (a := 12.0) (V := 217.516) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.505) (K := 22810.3) (Lb := 32.57791) (Lh := 48 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 48`
    rw [show 3 * (48 + 1) = 147 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 7 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 147) (a := 12.1244) (V := 217.026) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.526) (K := 22979.2) (Lb := 33.27106) (Lh := 49 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 49`
    rw [show 3 * (49 + 1) = 150 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 7 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 150) (a := 12.2475) (V := 216.555) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.546) (K := 23146.8) (Lb := 33.96421) (Lh := 50 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 50`
    rw [show 3 * (50 + 1) = 153 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 7 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 153) (a := 12.3694) (V := 216.103) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.566) (K := 23313.2) (Lb := 34.65735) (Lh := 51 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 51`
    rw [show 3 * (51 + 1) = 156 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 8 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 156) (a := 12.49) (V := 217.962) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.585) (K := 23948.5) (Lb := 35.3505) (Lh := 52 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 52`
    rw [show 3 * (52 + 1) = 159 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 8 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 159) (a := 12.6096) (V := 217.5) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.604) (K := 24110.4) (Lb := 36.04365) (Lh := 53 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 53`
    rw [show 3 * (53 + 1) = 162 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 8 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 162) (a := 12.728) (V := 217.056) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.623) (K := 24271.2) (Lb := 36.7368) (Lh := 54 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 54`
    rw [show 3 * (54 + 1) = 165 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 8 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 165) (a := 12.8453) (V := 216.628) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.641) (K := 24430.9) (Lb := 37.42994) (Lh := 55 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 55`
    rw [show 3 * (55 + 1) = 168 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 9 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 168) (a := 12.9615) (V := 218.344) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.659) (K := 25051.2) (Lb := 38.12309) (Lh := 56 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 56`
    rw [show 3 * (56 + 1) = 171 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 9 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 171) (a := 13.0767) (V := 217.908) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.677) (K := 25206.8) (Lb := 38.81624) (Lh := 57 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 57`
    rw [show 3 * (57 + 1) = 174 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 9 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 174) (a := 13.191) (V := 217.488) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.694) (K := 25361.7) (Lb := 39.50938) (Lh := 58 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 58`
    rw [show 3 * (58 + 1) = 177 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 9 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 177) (a := 13.3042) (V := 217.081) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.712) (K := 25515.4) (Lb := 40.20253) (Lh := 59 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 59`
    rw [show 3 * (59 + 1) = 180 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 10 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 180) (a := 13.4165) (V := 218.675) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.728) (K := 26122.4) (Lb := 40.89568) (Lh := 60 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `⌊log₂ n⌋ = 60`
    rw [show 3 * (60 + 1) = 183 by norm_num] at hPm h4d ⊢
    push_cast at hLE hLU ⊢
    have hm : m ≤ 10 := m_le_of hPm hlt (by norm_num)
    have hdU : d ≤ 42 := d_le42 hm1 hdj
    have hc := coef16_num (lam := 183) (a := 13.5278) (V := 218.263) (by norm_num) (by norm_num)
      (by norm_num) hm hd16 hdU hq (by norm_num) (by norm_num)
    push_cast at hc
    exact fin16 3 (x := 0.745) (K := 26272.6) (Lb := 41.58883) (Lh := 61 * 0.6931471808)
      (le_trans hc (by norm_num)) (by positivity)
      (by linarith) (by linarith) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Beyond `⌊log₂ n⌋ = 60` -/

/-- An upper bound of `e^x` for `0 ≤ x ≤ 1`. -/
theorem exp_le_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 100 := by
  have := Real.exp_bound' h0 h1 (n := 5) (by norm_num)
  have e : (∑ m ∈ Finset.range 5, x ^ m / (m.factorial : ℝ)) + x ^ 5 * ((5 : ℕ) + 1) /
      (((5 : ℕ).factorial : ℝ) * (5 : ℕ)) = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 100 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    ring
  linarith

/-- The depth for `λ ≥ 186`: `2.7725 m ≤ ln n - 13.5`. -/
theorem depth16_log {n m : ℕ} (hl : 186 ≤ GroupedOrder.lamN n)
    (h : 16 * GroupedOrder.lamN n * (16 * 4 ^ m) ^ 2 ≤ n) :
    27725 / 10000 * (m : ℝ) ≤ Real.log n - 135 / 10 := by
  have e : 16 * GroupedOrder.lamN n * (16 * 4 ^ m) ^ 2 = 4096 * GroupedOrder.lamN n * 2 ^ (4 * m) := by
    have e1 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    rw [e1, mul_pow, ← pow_mul]; ring_nf
  rw [e] at h
  have hpos : (0 : ℝ) < 4096 * GroupedOrder.lamN n := by
    have : (0 : ℝ) < GroupedOrder.lamN n := by exact_mod_cast (show 0 < GroupedOrder.lamN n by omega)
    linarith
  have h1 : (4096 * GroupedOrder.lamN n : ℝ) * (2 : ℝ) ^ (4 * m) ≤ n := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_pow] at h2
  have h3 : Real.log 761856 ≤ Real.log (4096 * GroupedOrder.lamN n : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (186 : ℝ) ≤ GroupedOrder.lamN n := by exact_mod_cast hl
    linarith
  have h4 : (135 / 10 : ℝ) ≤ Real.log 761856 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 761856)]
    have := Real.exp_one_lt_d9
    have e13 : Real.exp (135 / 10) = Real.exp 1 ^ 13 * Real.exp (1 / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h5 : Real.exp (1 / 2) ≤ 1.649 := by
      have := exp_le_taylor (x := 1 / 2) (by norm_num) (by norm_num)
      norm_num at this ⊢; linarith
    rw [e13]
    have hpow : Real.exp 1 ^ 13 ≤ 2.7182818286 ^ 13 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le this.le 13
    calc Real.exp 1 ^ 13 * Real.exp (1 / 2) ≤ 2.7182818286 ^ 13 * 1.649 :=
          mul_le_mul hpow h5 (Real.exp_pos _).le (by positivity)
      _ ≤ 761856 := by norm_num
  have hlog2 := Real.log_two_gt_d9
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e4 : (((4 * m : ℕ) : ℝ)) = 4 * (m : ℝ) := by push_cast; ring
  rw [e4] at h2
  have h6 : 27725 / 10000 * (m : ℝ) ≤ 4 * (m : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hlog2.le hm0
    linarith
  linarith

/-- The generic coefficient: `c ≤ 3743.5 r + 86.92 L + 2932 / r` for `r = √L`. -/
theorem gen16 {L r S mr qr ρ : ℝ} (hr : r ^ 2 = L) (hr0 : 6.5 ≤ r) (hSU : S ≤ 2.0977 * r)
    (hSD : 2.0803 * r ≤ S) (hD : 2.7725 * mr ≤ L - 13.5) (hm0 : 0 ≤ mr) (hq : qr ≤ 6 * mr + 42)
    (hq0 : 0 ≤ qr) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1.125) :
    1 + 8 * S * ρ * (172 + 53 * qr / S ^ 2) + 240.96 * (mr + 1) ≤
      3743.5 * r + 86.92 * L + 2932 / r := by
  have hrp : 0 < r := by linarith
  have hSp : 0 < S := by linarith
  set w := qr / S with hw
  have hwS : w * S = qr := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by positivity
  have e : 8 * S * ρ * (172 + 53 * qr / S ^ 2) = ρ * (1376 * S + 424 * w) := by
    rw [hw]; field_simp; ring
  rw [e]
  have hX : 0 ≤ 1376 * S + 424 * w := by positivity
  have h0 : ρ * (1376 * S + 424 * w) ≤ 1.125 * (1376 * S + 424 * w) :=
    mul_le_mul_of_nonneg_right hρ hX
  set u := 1 / r with hu
  have hu0 : 0 < u := by positivity
  have hru : r * u = 1 := by rw [hu]; field_simp
  -- `2.0803 w ≤ (6 m + 42) u`, `2.7725 m u ≤ r - 13.5 u`
  have h1 : 2.7725 * (mr * u) ≤ r - 13.5 * u := by
    have := mul_le_mul_of_nonneg_right hD hu0.le
    have e : (L - 13.5) * u = r - 13.5 * u := by
      rw [← hr]; have : r ^ 2 * u = r * (r * u) := by ring
      rw [sub_mul, this, hru]; ring
    linarith
  have h2 : 2.0803 * w ≤ 6 * (mr * u) + 42 * u := by
    have a : w * (2.0803 * r) ≤ w * S := mul_le_mul_of_nonneg_left hSD hw0
    have b : w * (2.0803 * r) ≤ 6 * mr + 42 := by linarith
    have c := mul_le_mul_of_nonneg_right b hu0.le
    have e : w * (2.0803 * r) * u = 2.0803 * w := by
      have : w * (2.0803 * r) * u = 2.0803 * w * (r * u) := by ring
      rw [this, hru, mul_one]
    linarith
  have h3 : 240.96 * mr ≤ 86.92 * (L - 13.5) := by linarith
  have h5 : 0 ≤ mr * u := by positivity
  have e2 : 2932 / r = 2932 * u := by rw [hu]; ring
  rw [e2]
  linarith

/-- `e^x` from below via `e · (series at x - 1)`. -/
theorem exp_ge_one_add {x : ℝ} (hx : 1 ≤ x) :
    2.7182818283 * (1 + (x - 1) + (x - 1) ^ 2 / 2 + (x - 1) ^ 3 / 6 + (x - 1) ^ 4 / 24 +
      (x - 1) ^ 5 / 120 + (x - 1) ^ 6 / 720) ≤ Real.exp x := by
  have h1 := exp_ge_taylor (show 0 ≤ x - 1 by linarith)
  have h2 : Real.exp x = Real.exp 1 * Real.exp (x - 1) := by rw [← Real.exp_add]; ring_nf
  rw [h2]
  exact mul_le_mul Real.exp_one_gt_d9.le h1 (by positivity) (Real.exp_pos _).le

/-- The generic range, `⌊log₂ n⌋ ≥ 61`: `c ≤ 940 L`, and `c ln L ≤ 2700 L` while `ln L ≤ 4.2`. -/
theorem gen16_final {L r t c : ℝ} (hL : 42.28 ≤ L) (hr : r = Real.sqrt L) (ht : t = Real.log L)
    (hc : c ≤ 3743.5 * r + 86.92 * L + 2932 / r) :
    c ≤ 940 * L ∧ (t ≤ 4.2 → c * t ≤ 2700 * L) := by
  have hL0 : 0 < L := by linarith
  have hr2 : r ^ 2 = L := by rw [hr]; exact Real.sq_sqrt hL0.le
  have hr0 : 6.5 ≤ r := by
    rw [hr, show (6.5 : ℝ) = Real.sqrt (6.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hrp : 0 < r := by linarith
  have hrL : r * r = L := by rw [← hr2]; ring
  have hinv : 2932 / r ≤ 452 := by rw [div_le_iff₀ hrp]; linarith
  refine ⟨?_, fun ht42 => ?_⟩
  · -- `3743.5 r ≤ 576 L` since `r ≥ 6.5`
    have : 3743.5 * r ≤ 576 * L := by nlinarith
    linarith
  · -- `t ≤ 0.5818 r`
    have hrt : r = Real.exp (t / 2) := by
      rw [hr, ht]
      have e : L = Real.exp (Real.log L / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast
        rw [show (2 : ℝ) * (Real.log L / 2) = Real.log L by ring, Real.exp_log hL0]
      conv_lhs => rw [e]
      rw [Real.sqrt_sq (Real.exp_pos _).le]
    have ht37 : 3.7 ≤ t := by
      rw [ht, Real.le_log_iff_exp_le hL0]
      have e : Real.exp 3.7 = Real.exp 1 ^ 3 * Real.exp 0.7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h7 : Real.exp 0.7 ≤ 2.0139 := by
        have := exp_le_taylor (x := 0.7) (by norm_num) (by norm_num)
        norm_num at this ⊢; linarith
      have hpow : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
      rw [e]
      calc Real.exp 1 ^ 3 * Real.exp 0.7 ≤ 2.7182818286 ^ 3 * 2.0139 :=
            mul_le_mul hpow h7 (Real.exp_pos _).le (by positivity)
        _ ≤ 42.28 := by norm_num
        _ ≤ L := hL
    have hE : (6.3596 : ℝ) ≤ Real.exp (3.7 / 2) := by
      have := exp_ge_one_add (x := 3.7 / 2) (by norm_num)
      norm_num at this ⊢; linarith
    have hm := mul_le_exp_half (by norm_num) ht37 (by norm_num) hE
    rw [← hrt] at hm
    -- `c t ≤ 3743.5 r t + 86.92 L t + 2932 t / r`
    have ht0 : 0 ≤ t := by linarith
    have hct : c * t ≤ (3743.5 * r + 86.92 * L + 2932 / r) * t := mul_le_mul_of_nonneg_right hc ht0
    have a1 : 3743.5 * r * t ≤ 3743.5 * r * (3.7 / 6.3596 * r) := by
      have : t ≤ 3.7 / 6.3596 * r := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have a2 : 86.92 * L * t ≤ 86.92 * L * 4.2 := mul_le_mul_of_nonneg_left ht42 (by positivity)
    have a3 : 2932 / r * t ≤ 452 * 4.2 := mul_le_mul hinv ht42 ht0 (by norm_num)
    have e : (3743.5 * r + 86.92 * L + 2932 / r) * t =
        3743.5 * r * t + 86.92 * L * t + 2932 / r * t := by ring
    have e2 : 3743.5 * r * (3.7 / 6.3596 * r) = 3743.5 * 3.7 / 6.3596 * L := by rw [← hrL]; ring
    nlinarith

/-- `29 L + 4900 √L ≤ 2700 L / ln L` for `4.2 ≤ ln L ≤ 42`. -/
theorem mid_coef {L : ℝ} (hL0 : 0 < L) (ht1 : 4.2 ≤ Real.log L) (ht : Real.log L ≤ 42) :
    29 * L + 4900 * Real.sqrt L ≤ 2700 * L / Real.log L := by
  set t := Real.log L with htd
  set r := Real.sqrt L with hrd
  have hr : r = Real.exp (t / 2) := by
    have e : L = Real.exp (t / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast
      rw [show (2 : ℝ) * (t / 2) = t by ring, htd, Real.exp_log hL0]
    rw [hrd, e, Real.sqrt_sq (Real.exp_pos _).le]
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hLr : L = r * r := by rw [hrd, Real.mul_self_sqrt hL0.le]
  have key : 29 * r * t + 4900 * t ≤ 2700 * r := by
    rcases le_or_gt t 6 with hB | hB
    · have hE : (8.1661 : ℝ) ≤ Real.exp (4.2 / 2) := by
        have e : Real.exp (4.2 / 2) = Real.exp 1 ^ 2 * Real.exp 0.1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
        have h1 := exp_ge_taylor (x := 0.1) (by norm_num)
        have h2 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
          pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
        rw [e]
        have := mul_le_mul h2 h1 (by norm_num) (by positivity)
        norm_num at this ⊢; linarith
      have := mul_le_exp_half (by norm_num) ht1 (by norm_num) hE
      rw [← hr] at this
      have h2 : r * t ≤ r * 6 := mul_le_mul_of_nonneg_left hB hr0.le
      nlinarith
    · have h3lo : (20.0855 : ℝ) ≤ Real.exp (6 / 2) := by
        have := exp_one_pow_ge 3; push_cast at this; norm_num at this ⊢; linarith
      have := mul_le_exp_half (by norm_num) hB.le (by norm_num) h3lo
      rw [← hr] at this
      have h2 : r * t ≤ r * 42 := mul_le_mul_of_nonneg_left ht hr0.le
      nlinarith
  have htpos : 0 < t := by linarith
  rw [le_div_iff₀ htpos, hLr]
  have := mul_le_mul_of_nonneg_left key hr0.le
  nlinarith

/-! ## The uniform bounds -/

set_option maxHeartbeats 1000000 in
/-- The coefficient of the grid of free level `≥ 16`: at most `940 L`, and `2700 L / ln L`
while `ln L ≤ 4.2`. -/
theorem deep16_coef {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (Bd : ReachableBoard n) :
    ∃ c : ℝ, 0 ≤ c ∧ (optimalLength Bd : ℝ) ≤ (manhattan Bd.val : ℝ) + c * (n : ℝ) ^ ((5 : ℝ) / 2) ∧
      c ≤ 940 * Real.log n ∧
      (Real.log (Real.log n) ≤ 4.2 → c * Real.log (Real.log n) ≤ 2700 * Real.log n) := by
  obtain ⟨m, d, q, hm1, hPm, h4d, hd16, hdj, hq, hopt⟩ := port_coef16 hn Bd
  refine ⟨_, by positivity, hopt, ?_⟩
  rcases Nat.lt_or_ge (Nat.log 2 n) 61 with hE | hE
  · obtain ⟨h1, h2⟩ := coef16_small hn (by omega) hm1 hPm h4d hd16 hdj hq
    exact ⟨h1, fun _ => h2⟩
  -- the generic range
  have hlam : GroupedOrder.lamN n = 3 * (Nat.log 2 n + 1) := rfl
  have hl186 : 186 ≤ GroupedOrder.lamN n := by rw [hlam]; omega
  have hD := depth16_log (m := m) hl186 hPm
  have hn1 : 1 ≤ n := by omega
  have hlamL := lam_le_log hn1
  have hlamG := lam_ge_log hn1
  have hge : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  set L := Real.log n with hLd
  have hL : 42.28 ≤ L := by
    have c' : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    push_cast at c'
    have := Real.log_le_log (by positivity) c'
    rw [Real.log_pow] at this
    have h2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le
      (show (0 : ℝ) ≤ (Nat.log 2 n : ℝ) by positivity)
    have : (61 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hE
    linarith
  set r := Real.sqrt L with hrd
  have hr2 : r ^ 2 = L := Real.sq_sqrt (by linarith)
  have hr0 : 6.5 ≤ r := by
    rw [hrd, show (6.5 : ℝ) = Real.sqrt (6.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  set lr : ℝ := (GroupedOrder.lamN n : ℝ) with hlr
  have hlr0 : 0 < lr := by rw [hlr]; exact_mod_cast (show 0 < GroupedOrder.lamN n by omega)
  set S := Real.sqrt lr with hS
  have hS2 : S ^ 2 = lr := Real.sq_sqrt hlr0.le
  have hSU : S ≤ 2.0977 * r := by
    have h1 : lr ≤ 4.4 * L := by linarith
    calc S ≤ Real.sqrt (4.4 * L) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 4.4 * Real.sqrt L := Real.sqrt_mul (by norm_num) _
      _ ≤ 2.0977 * r := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [show (2.0977 : ℝ) = Real.sqrt (2.0977 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
  have hSD : 2.0803 * r ≤ S := by
    have h1 : 4.328 * L ≤ lr := by linarith
    calc 2.0803 * r ≤ Real.sqrt 4.328 * Real.sqrt L := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [show (2.0803 : ℝ) = Real.sqrt (2.0803 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
      _ = Real.sqrt (4.328 * L) := (Real.sqrt_mul (by norm_num) _).symm
      _ ≤ S := Real.sqrt_le_sqrt h1
  have hd42 := d_le42 hm1 hdj
  have hqr : (q : ℝ) ≤ 6 * (m : ℝ) + 42 := by exact_mod_cast (show q ≤ 6 * m + 42 by omega)
  have hdR : (16 : ℝ) ≤ d := by exact_mod_cast hd16
  have hρ1 : 1 ≤ 1 + 2 / (d : ℝ) := by
    have : 0 ≤ 2 / (d : ℝ) := by positivity
    linarith
  have hρ : 1 + 2 / (d : ℝ) ≤ 1.125 := by
    have : 2 / (d : ℝ) ≤ 2 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdR
    linarith
  have hg := gen16 hr2 hr0 hSU hSD (by linarith) (Nat.cast_nonneg m) hqr
    (Nat.cast_nonneg q) hρ1 hρ
  rw [hS2] at hg
  obtain ⟨g1, g2⟩ := gen16_final hL hrd rfl hg
  exact ⟨g1, g2⟩

/-- **`OPT(B) ≤ M(B) + 940 n^(5/2) ln n`** for `n ≥ 2²³`. -/
theorem port_approximation_uniform {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + 940 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n := by
  obtain ⟨c, -, hopt, hc, -⟩ := deep16_coef hn B
  have hP : (0 : ℝ) ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
  have := mul_le_mul_of_nonneg_right hc hP
  have e : 940 * Real.log n * (n : ℝ) ^ ((5 : ℝ) / 2) =
      940 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n := by ring
  linarith

/-- **`OPT(B) ≤ M(B) + 2700 n^(5/2) ln n / ln ln n`** for `n ≥ 2²³`: the grid of free level
`≥ 16` for `ln ln n ≤ 4.2`, `port_optimalLength_le` up to `log₂ n < 2⁶⁰`, `port_loglog`
beyond. -/
theorem port_loglog_uniform {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (Bd : ReachableBoard n) :
    (optimalLength Bd : ℝ) ≤ (manhattan Bd.val : ℝ) +
      2700 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n / Real.log (Real.log n) := by
  have hL := log_ge_of_pow23 hn
  set L := Real.log n with hLd
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < Real.log L := Real.log_pos (by linarith)
  set P : ℝ := (n : ℝ) ^ ((5 : ℝ) / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  have hX : 0 ≤ P * L / Real.log L := by positivity
  have e2 : 2700 * P * L / Real.log L = 2700 * L / Real.log L * P := by ring
  by_cases hE : 2 ^ 60 ≤ Nat.log 2 n
  · have h := port_loglog_log hE Bd
    rw [← hLd, ← hP] at h
    have e1 : 242 * P * L / Real.log L = 242 * (P * L / Real.log L) := by ring
    have e3 : 2700 * P * L / Real.log L = 2700 * (P * L / Real.log L) := by ring
    rw [e1] at h; rw [e3]
    linarith
  push Not at hE
  by_cases ht : Real.log L ≤ 4.2
  · obtain ⟨c, hc0, hopt, -, hct⟩ := deep16_coef hn Bd
    rw [← hP] at hopt
    have h1 : c ≤ 2700 * L / Real.log L := by
      rw [le_div_iff₀ ht0]; exact hct ht
    have := mul_le_mul_of_nonneg_right h1 hP0
    rw [e2]; linarith
  push Not at ht
  -- `ln L ≤ 42` below `2^(2⁶⁰)`
  set E := Nat.log 2 n with hEd
  have hnE : n < 2 ^ (E + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hE1 : ((E : ℝ) + 1) ≤ 2 ^ 60 := by exact_mod_cast (show E + 1 ≤ 2 ^ 60 by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLE : L ≤ ((E : ℝ) + 1) * Real.log 2 := by
    have : (n : ℝ) ≤ ((2 : ℝ) ^ (E + 1)) := by exact_mod_cast hnE.le
    have := Real.log_le_log hn0 this
    rw [Real.log_pow] at this; push_cast at this; exact this
  have ht42 : Real.log L ≤ 42 := by
    rw [Real.log_le_iff_le_exp hL0]
    have h42 := exp_one_pow_ge 42
    push_cast at h42
    have hl2 := Real.log_two_lt_d9
    have : ((E : ℝ) + 1) * Real.log 2 ≤ 2 ^ 60 * 0.6931471808 :=
      mul_le_mul hE1 hl2.le (Real.log_nonneg (by norm_num)) (by positivity)
    norm_num at h42 this
    linarith
  have hc := mid_coef hL0 ht.le ht42
  have h := port_optimalLength_le hn Bd
  rw [← hLd, ← hP] at h
  have := mul_le_mul_of_nonneg_right hc hP0
  rw [e2]
  linarith

end SlidingPuzzle.Port
