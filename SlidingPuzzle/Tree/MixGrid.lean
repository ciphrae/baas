import SlidingPuzzle.Tree.HierMix
import SlidingPuzzle.Tree.Final
import SlidingPuzzle.Tree.GridChoice

/-! # The mixed grid: levels of branching `b + 2` and `b`

`Bmix b j` branches `b + 2` at the levels `ℓ < j` and `b` below, so `k = (b+2)^j b^(h-j)`
and `q = h b + 2j`. Consecutive `j` change `k` by the factor `(b+2)/b` only, which
removes the rounding loss of a uniform grid. -/
namespace SlidingPuzzle.Tree

open Finset

namespace HierMix

theorem sum_le_prod (B : ℕ → ℕ) (hB : ∀ ℓ, 2 ≤ B ℓ) :
    ∀ h, ∑ ℓ ∈ range h, B ℓ ≤ ∏ ℓ ∈ range h, B ℓ ∧ (h = 0 ∨ 2 ≤ ∏ ℓ ∈ range h, B ℓ)
  | 0 => by simp
  | h + 1 => by
    obtain ⟨ih1, ih2⟩ := sum_le_prod B hB h
    rw [sum_range_succ, prod_range_succ]
    have hb := hB h
    rcases ih2 with h0 | h2
    · subst h0; simp; omega
    · refine ⟨?_, Or.inr ?_⟩
      · nlinarith
      · nlinarith

theorem nq_le_sz {B : ℕ → ℕ} {h : ℕ} (hB : ∀ ℓ, 2 ≤ B ℓ) : nq B h ≤ sz B h 0 := by
  have e1 : nq B h = ∑ ℓ ∈ range h, B ℓ := Fin.sum_univ_eq_sum_range B h
  have e2 : sz B h 0 = ∏ ℓ ∈ range h, B ℓ := by unfold sz; rw [range_eq_Ico]
  rw [e1, e2]; exact (sum_le_prod B hB h).1

end HierMix

/-- Branching `b + 2` at the levels `ℓ < j`, `b` below. -/
def Bmix (b j : ℕ) (ℓ : ℕ) : ℕ := if ℓ < j then b + 2 else b

theorem Bmix_ge {b : ℕ} (hb : 2 ≤ b) (j ℓ : ℕ) : 2 ≤ Bmix b j ℓ := by
  unfold Bmix; split_ifs <;> omega

theorem prod_Bmix (b j : ℕ) : ∀ h, ∏ ℓ ∈ range h, Bmix b j ℓ =
    (b + 2) ^ (min j h) * b ^ (h - min j h)
  | 0 => by simp
  | h + 1 => by
    rw [prod_range_succ, prod_Bmix b j h]
    unfold Bmix
    split_ifs with hl
    · rw [show min j (h + 1) = min j h + 1 by omega, show h + 1 - (min j h + 1) = h - min j h by omega]
      ring
    · rw [show min j (h + 1) = min j h by omega, show h + 1 - min j h = h - min j h + 1 by omega]
      ring

theorem sum_Bmix (b j : ℕ) : ∀ h, ∑ ℓ ∈ range h, Bmix b j ℓ = h * b + 2 * min j h
  | 0 => by simp
  | h + 1 => by
    rw [sum_range_succ, sum_Bmix b j h]
    unfold Bmix
    split_ifs with hl
    · rw [show min j (h + 1) = min j h + 1 by omega]; ring
    · rw [show min j (h + 1) = min j h by omega]; ring

theorem sz_Bmix {b j h : ℕ} (hj : j ≤ h) :
    HierMix.sz (Bmix b j) h 0 = (b + 2) ^ j * b ^ (h - j) := by
  unfold HierMix.sz; rw [← range_eq_Ico, prod_Bmix, min_eq_left hj]

theorem nq_Bmix {b j h : ℕ} (hj : j ≤ h) : HierMix.nq (Bmix b j) h = h * b + 2 * j := by
  rw [HierMix.nq, Fin.sum_univ_eq_sum_range (Bmix b j) h, sum_Bmix, min_eq_left hj]

/-- `2 λ ≤ h b` for `b ≥ 256` and `n ≤ 8h (2b)^(2h+1)`, with no condition relating `b` and `h`. -/
theorem log_slack_mix {m b h : ℕ} (hh : 1 ≤ h) (hb : 256 ≤ b)
    (hm : m ≤ 8 * h * (2 * b) ^ (2 * h + 1)) : 2 * GroupedOrder.lamN m ≤ h * b := by
  set L := Nat.log 2 b with hL
  have hbL : b < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) b
  have hL8 : 8 ≤ L := by
    rw [hL]
    exact Nat.le_log_of_pow_le (by decide) (le_trans (by norm_num) hb)
  have hLb : 24 * L + 54 ≤ b :=
    (log_linear_le L hL8).trans (Nat.pow_log_le_self 2 (by omega))
  have h2b : 2 * b < 2 ^ (L + 2) := by rw [pow_succ]; omega
  have hh2 : h < 2 ^ h := Nat.lt_two_pow_self
  have hm2 : m < 2 ^ (3 + h + (L + 2) * (2 * h + 1)) := by
    calc m ≤ 8 * h * (2 * b) ^ (2 * h + 1) := hm
      _ < 8 * 2 ^ h * (2 ^ (L + 2)) ^ (2 * h + 1) := by
          apply Nat.mul_lt_mul_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hh2 (by norm_num))
            (Nat.pow_le_pow_left h2b.le _) (by positivity)
      _ = _ := by rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
  have hlog : Nat.log 2 m < 3 + h + (L + 2) * (2 * h + 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    exact Nat.log_lt_of_lt_pow (by omega) hm2
  unfold GroupedOrder.lamN
  have h2 : h * (24 * L + 54) ≤ h * b := Nat.mul_le_mul_left h hLb
  nlinarith

/-- The mixed grid for `n ≥ 8h·256^(2h+1)`: the largest even `b` with `8h b^(2h+1) ≤ n`,
then the largest `j` with `8 q k² ≤ n`; the next `j` fails. -/
theorem exists_mix (h : ℕ) (hh : 1 ≤ h) (n : ℕ) (hn : 8 * h * 256 ^ (2 * h + 1) ≤ n) :
    ∃ b j, Even b ∧ 256 ≤ b ∧ j < h ∧ 8 * h * b ^ (2 * h + 1) ≤ n ∧
      n < 8 * h * (b + 2) ^ (2 * h + 1) ∧
      8 * (h * b + 2 * j) * ((b + 2) ^ j * b ^ (h - j)) ^ 2 ≤ n ∧
      n < 8 * (h * b + 2 * j + 2) * ((b + 2) ^ (j + 1) * b ^ (h - (j + 1))) ^ 2 := by
  classical
  set t := Nat.findGreatest (fun t => 8 * h * (2 * t) ^ (2 * h + 1) ≤ n) n with ht
  have h128 : 128 ≤ n := by
    have : 128 ≤ 8 * h * 256 ^ (2 * h + 1) := by
      have : 256 ≤ 256 ^ (2 * h + 1) := Nat.le_self_pow (by omega) _
      nlinarith
    omega
  have hP128 : 8 * h * (2 * 128) ^ (2 * h + 1) ≤ n := by simpa using hn
  have ht128 : 128 ≤ t := Nat.le_findGreatest h128 hP128
  have hPt : 8 * h * (2 * t) ^ (2 * h + 1) ≤ n :=
    Nat.findGreatest_spec (P := fun t => 8 * h * (2 * t) ^ (2 * h + 1) ≤ n) h128 hP128
  have hnt : n < 8 * h * (2 * (t + 1)) ^ (2 * h + 1) := by
    have hle : t + 1 ≤ n := by
      have : 2 * t ≤ (2 * t) ^ (2 * h + 1) := Nat.le_self_pow (by omega) _
      have : (2 * t) ^ (2 * h + 1) ≤ 8 * h * (2 * t) ^ (2 * h + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have := Nat.findGreatest_is_greatest (P := fun t => 8 * h * (2 * t) ^ (2 * h + 1) ≤ n)
      (Nat.lt_succ_self t) hle
    simpa using this
  set b := 2 * t with hb
  have hb2 : 2 * (t + 1) = b + 2 := by omega
  rw [hb2] at hnt
  let P : ℕ → Prop := fun j => 8 * (h * b + 2 * j) * ((b + 2) ^ j * b ^ (h - j)) ^ 2 ≤ n
  set j := Nat.findGreatest P h with hj
  have hP0 : P 0 := by
    show 8 * (h * b + 2 * 0) * ((b + 2) ^ 0 * b ^ (h - 0)) ^ 2 ≤ n
    have : 8 * (h * b + 2 * 0) * ((b + 2) ^ 0 * b ^ (h - 0)) ^ 2 = 8 * h * b ^ (2 * h + 1) := by
      rw [Nat.sub_zero, pow_zero, one_mul, ← pow_mul, pow_succ]; ring
    rw [this]; exact hPt
  have hPj : P j := Nat.findGreatest_spec (P := P) (Nat.zero_le h) hP0
  have hjh : j ≤ h := Nat.findGreatest_le h
  have hPh : ¬ P h := by
    show ¬ 8 * (h * b + 2 * h) * ((b + 2) ^ h * b ^ (h - h)) ^ 2 ≤ n
    have : 8 * (h * b + 2 * h) * ((b + 2) ^ h * b ^ (h - h)) ^ 2 = 8 * h * (b + 2) ^ (2 * h + 1) := by
      rw [Nat.sub_self, pow_zero, mul_one, ← pow_mul, pow_succ]; ring
    rw [this]; omega
  have hjlt : j < h := by
    rcases Nat.lt_or_ge j h with h1 | h1
    · exact h1
    · exact absurd (show j = h by omega ▸ hPj) hPh
  have hPj1 : ¬ P (j + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self j) (by omega)
  refine ⟨b, j, ⟨t, by omega⟩, by omega, hjlt, hPt, hnt, hPj, ?_⟩
  simp only [P, not_le] at hPj1
  have e : h * b + 2 * (j + 1) = h * b + 2 * j + 2 := by ring
  rw [e] at hPj1
  exact hPj1

open SlidingPuzzle in
/-- The tree bound on the mixed grid. -/
theorem optimalLength_le_mix {n b j h : ℕ} [NeZero n] (hh : 1 ≤ h) (hbe : Even b)
    (hb : 256 ≤ b) (hj : j < h) (hhi : n ≤ 8 * h * (2 * b) ^ (2 * h + 1))
    (hlo : 8 * (h * b + 2 * j) * ((b + 2) ^ j * b ^ (h - j)) ^ 2 ≤ n) (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * ((b + 2) ^ j * b ^ (h - j))) +
      2 * (50 * (h + 3) * ((b + 2) ^ j * b ^ (h - j)) ^ 2 * (n / ((b + 2) ^ j * b ^ (h - j))) ^ 3) := by
  have hb2 : 2 ≤ b := by omega
  have hB := Bmix_ge hb2 j
  have hsz := sz_Bmix (b := b) (h := h) hj.le
  have hnq := nq_Bmix (b := b) (h := h) hj.le
  have hqk := HierMix.nq_le_sz (B := Bmix b j) (h := h) hB
  rw [hsz, hnq] at hqk
  have hbk : b ≤ (b + 2) ^ j * b ^ (h - j) := by
    have h1 : b ≤ b ^ (h - j) := by
      calc b = b ^ 1 := (pow_one b).symm
        _ ≤ b ^ (h - j) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 1 ≤ (b + 2) ^ j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hres := optimalLength_le_lanes (h := h) (HierMix.sys (Bmix b j) h hB hh) rfl hh
    (by rw [hsz]; exact (hbe.pow_of_ne_zero (by omega)).mul_left _)
    (by rw [hnq]; obtain ⟨c, hc⟩ := hbe; exact ⟨h * c + j, by rw [hc]; ring⟩)
    (by rw [hsz, hnq]; exact hqk) (by rw [hsz]; omega)
    (by rw [hnq]; nlinarith)
    (by rw [hnq]; have := log_slack_mix hh hb hhi; omega)
    (by rw [hsz, hnq]; have e : 8 * ((b + 2) ^ j * b ^ (h - j)) * (h * b + 2 * j) *
          ((b + 2) ^ j * b ^ (h - j)) = 8 * (h * b + 2 * j) * ((b + 2) ^ j * b ^ (h - j)) ^ 2 := by
          ring
        omega) B
  rw [hsz] at hres
  exact hres

theorem final_arith_mix {h O M A T Y S P : ℝ} (hh : 0 ≤ h)
    (hO : O ≤ M + 2 * A + 2 * (50 * (h + 3) * T)) (hA : A ≤ 1 / 128 * Y)
    (hT : 100 * (h + 3) * T ≤ 100 * (h + 3) * Y) (hY : Y ≤ 1.012 * S * P)
    (hS : 0 ≤ S) (hP : 0 ≤ P) :
    O ≤ M + 102 * (h + 3) * S * P := by
  have hSP : 0 ≤ S * P := mul_nonneg hS hP
  have h1 : O ≤ M + (100 * (h + 3) + 1 / 64) * Y := by nlinarith
  have h2 : (100 * (h + 3) + 1 / 64) * Y ≤ (100 * (h + 3) + 1 / 64) * (1.012 * S * P) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  nlinarith

theorem sqrt_le_root {h : ℕ} (hh : 1 ≤ h) {b n : ℝ} (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hlo : 8 * (h : ℝ) * b ^ (2 * h + 1) ≤ n) : Real.sqrt b ≤ n ^ (1 / (4 * (h : ℝ) + 2)) := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hp : 0 ≤ b ^ (2 * h + 1) := pow_nonneg hb _
  have h1 : b ^ (2 * h + 1) ≤ n := by nlinarith
  have h2 := Real.rpow_le_rpow hp h1 (show (0 : ℝ) ≤ 1 / (4 * (h : ℝ) + 2) by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb] at h2
  rw [Real.sqrt_eq_rpow]
  have e : ((2 * h + 1 : ℕ) : ℝ) * (1 / (4 * (h : ℝ) + 2)) = 1 / 2 := by
    push_cast; field_simp; ring
  rwa [e] at h2

open SlidingPuzzle in
/-- **The explicit tree bound on mixed grids** at depth `h ≥ 1`: for `n ≥ 8h·256^(2h+1)`,
`OPT(B) ≤ M(B) + 102 (h+3) √(8h) n^(5/2 + 1/(4h+2))`. -/
theorem tree_uniform_approximation_explicit (h : ℕ) (hh : 1 ≤ h) {n : ℕ} [NeZero n]
    (hn : 8 * h * 256 ^ (2 * h + 1) ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      102 * ((h : ℝ) + 3) * Real.sqrt (8 * h) * (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) := by
  obtain ⟨b, j, hbe, hb, hj, hlo1, hhi1, hlo, hhi⟩ := exists_mix h hh n hn
  have hhi' : n ≤ 8 * h * (2 * b) ^ (2 * h + 1) :=
    hhi1.le.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hnat := optimalLength_le_mix hh hbe hb hj hhi' hlo B
  set K := (b + 2) ^ j * b ^ (h - j) with hK
  -- `n b² ≤ 8h (b+2)³ K²`
  have hkey : n * b ^ 2 ≤ 8 * h * (b + 2) ^ 3 * K ^ 2 := by
    have e1 : (b + 2) ^ (j + 1) * b ^ (h - (j + 1)) * b = K * (b + 2) := by
      rw [hK]
      have : h - j = h - (j + 1) + 1 := by omega
      rw [this, pow_succ, pow_succ]; ring
    have hq : h * b + 2 * j + 2 ≤ h * (b + 2) := by nlinarith
    have h1 : n * b ^ 2 ≤ 8 * (h * b + 2 * j + 2) * ((b + 2) ^ (j + 1) * b ^ (h - (j + 1)) * b) ^ 2 := by
      have := Nat.mul_le_mul_right (b ^ 2) hhi.le
      calc n * b ^ 2 ≤ _ := this
        _ = _ := by ring
    rw [e1] at h1
    calc n * b ^ 2 ≤ _ := h1
      _ ≤ 8 * (h * (b + 2)) * (K * (b + 2)) ^ 2 := by gcongr
      _ = _ := by ring
  have hqK : 2048 * K ^ 2 ≤ n := by
    have : 2048 ≤ 8 * (h * b + 2 * j) := by nlinarith
    calc 2048 * K ^ 2 ≤ 8 * (h * b + 2 * j) * K ^ 2 := Nat.mul_le_mul_right _ this
      _ ≤ n := hlo
  have hK256 : 256 ≤ K := by
    have h1 : b ≤ b ^ (h - j) := by
      calc b = b ^ 1 := (pow_one b).symm
        _ ≤ b ^ (h - j) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 1 ≤ (b + 2) ^ j := Nat.one_le_pow _ _ (by omega)
    rw [hK]; nlinarith
  -- reals
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set Kr : ℝ := (K : ℝ) with hKr
  have hKpos : 0 < Kr := by rw [hKr]; exact_mod_cast (show 0 < K by omega)
  have hK256r : (256 : ℝ) ≤ Kr := by rw [hKr]; exact_mod_cast hK256
  have hks : Kr * ((n / K : ℕ) : ℝ) ≤ n := by
    have : K * (n / K) ≤ n := Nat.mul_div_le n _
    rw [hKr]; exact_mod_cast this
  have hterm2 : Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / Kr := by
    rw [le_div_iff₀ hKpos]
    have := pow_le_pow_left₀ (by positivity) hks 3
    nlinarith [this]
  have hK2 : 2048 * Kr ^ 2 ≤ n := by rw [hKr]; exact_mod_cast hqK
  have hn3003 : (3003 : ℝ) ≤ n := by nlinarith
  have hterm1 : (15 * (n : ℝ) ^ 2 + 3002 * n + 1) * Kr ≤ (1 / 128) * ((n : ℝ) ^ 3 / Kr) := by
    have ha : 15 * (n : ℝ) ^ 2 + 3002 * n + 1 ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
    have hb' : 2048 * ((n : ℝ) ^ 2 * Kr) ≤ (n : ℝ) ^ 3 / Kr := by
      rw [le_div_iff₀ hKpos]
      nlinarith [mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_right ha hKpos.le]
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * (n : ℝ) ^ 2 + 3002 * n + 1) * Kr) +
      2 * (50 * ((h : ℝ) + 3) * (Kr ^ 2 * ((n / K : ℕ) : ℝ) ^ 3)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    rw [hKr]
    linarith [this]
  -- `√n / K ≤ 1.012 √(8h) √b`
  have hbr : (256 : ℝ) ≤ b := by exact_mod_cast hb
  have hkeyr : (n : ℝ) * (b : ℝ) ^ 2 ≤ 8 * h * ((b : ℝ) + 2) ^ 3 * Kr ^ 2 := by
    rw [hKr]; exact_mod_cast hkey
  have hcube : ((b : ℝ) + 2) ^ 3 ≤ 1.012 ^ 2 * (b : ℝ) ^ 3 := by nlinarith
  have hsq : (n : ℝ) ≤ (1.012 ^ 2 * (8 * h * b)) * Kr ^ 2 := by
    have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
    have : (n : ℝ) * (b : ℝ) ^ 2 ≤ (1.012 ^ 2 * (8 * h * b)) * Kr ^ 2 * (b : ℝ) ^ 2 := by
      calc (n : ℝ) * (b : ℝ) ^ 2 ≤ 8 * h * ((b : ℝ) + 2) ^ 3 * Kr ^ 2 := hkeyr
        _ ≤ 8 * h * (1.012 ^ 2 * (b : ℝ) ^ 3) * Kr ^ 2 := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hb2
  have hsqrt : Real.sqrt n ≤ 1.012 * Real.sqrt (8 * h) * Real.sqrt b * Kr := by
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKpos.le, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), Real.sqrt_mul (by positivity)] at this
    linarith
  -- `√b ≤ n^(1/(4h+2))`
  have hroot : Real.sqrt b ≤ (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) :=
    sqrt_le_root hh (by positivity) hn0.le (by exact_mod_cast hlo1)
  have hmain : (n : ℝ) ^ 3 / Kr ≤ 1.012 * Real.sqrt (8 * h) *
      (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) := by
    rw [div_le_iff₀ hKpos, Real.rpow_add hn0]
    have e3 : (n : ℝ) ^ 3 = (n : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt n := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0, ← Real.rpow_natCast]; norm_num
    rw [e3]
    have hP : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 2) := by positivity
    have h8 : 0 ≤ Real.sqrt (8 * h) := Real.sqrt_nonneg _
    calc (n : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt n
        ≤ (n : ℝ) ^ ((5 : ℝ) / 2) * (1.012 * Real.sqrt (8 * h) * Real.sqrt b * Kr) :=
          mul_le_mul_of_nonneg_left hsqrt hP
      _ ≤ (n : ℝ) ^ ((5 : ℝ) / 2) * (1.012 * Real.sqrt (8 * h) *
            (n : ℝ) ^ (1 / (4 * (h : ℝ) + 2)) * Kr) := by gcongr
      _ = _ := by ring
  exact final_arith_mix (h := (h : ℝ)) (by positivity) hcast hterm1
    (mul_le_mul_of_nonneg_left hterm2 (by positivity)) hmain (Real.sqrt_nonneg _) (by positivity)

open SlidingPuzzle in
/-- Depth `h`: `OPT(B) ≤ M(B) + C n^(5/2 + 1/(4h+2))` for all large `n`. -/
theorem tree_uniform_approximation (h : ℕ) (hh : 1 ≤ h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
          C * (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) :=
  ⟨102 * ((h : ℝ) + 3) * Real.sqrt (8 * h), by positivity, 8 * h * 256 ^ (2 * h + 1),
    fun n hn hn2 =>
    letI : NeZero n := ⟨by omega⟩
    fun B => tree_uniform_approximation_explicit h hh hn B⟩

open SlidingPuzzle in
/-- **The exponent `5/2 + ε`**: for every `ε > 0`, `OPT(B) ≤ M(B) + C n^(5/2 + ε)`. -/
theorem tree_exponent {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * (n : ℝ) ^ (5 / 2 + ε) := by
  obtain ⟨h, hh, hle⟩ := exists_depth_for_slack hε
  obtain ⟨C, hC, N, hN⟩ := tree_uniform_approximation h hh
  refine ⟨C, hC, N, fun n hn hn2 B => ?_⟩
  have h1 := hN n hn hn2 B
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have := Real.rpow_le_rpow_of_exponent_le hn1 hle
  have := mul_le_mul_of_nonneg_left this hC
  linarith

end SlidingPuzzle.Tree
