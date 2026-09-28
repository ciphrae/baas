import SlidingPuzzle.Hub.AsympBound

/-! # The hub algorithm without the logarithm: natural-number bounds

The in-flight budget is linear in `n` (`Rhub`), so the hub algorithm on side
`n = k*s` costs `O(n²s + k²n²)` (`hubBound_le_lin`) and `k ≍ n^(1/3)` gives
`O(n^(8/3))`. The capacity condition `76kλ_A ≤ 5s` still involves
`λ_A = log₂(k³s²) + 4 ≤ log₂(kn²) + 4`; near the threshold it limits `k`. Take
`k = 2m` with `m` the largest integer such that `304 m² Λ(m) + 10 m ≤ 5n`,
`Λ(m) = log₂(2m n²) + 4` (capacity), and `64 m³ ≤ n` (cube scale).

For `n ≥ linN = 10⁷` this grid has `m ≥ 50` (`exists_lin_width`), and
`optimalLength_le_lin_nat` bounds the solution length by
`M + 2 (hubLinKX X + hubLinKW W)/1000 + 2 Z` with `X = n²s`, `W = k²n²` and `Z`
the prefix cost. -/
namespace SlidingPuzzle.Hub

open SlidingPuzzle

/-- The side from which the hub algorithm is used for the bound without the logarithm. -/
def linN : ℕ := 10 ^ 7

/-- The capacity term of the grid. -/
def gridCap (n m : ℕ) : ℕ := 304 * m ^ 2 * (Nat.log 2 (2 * m * n ^ 2) + 4) + 10 * m

/-- `m = 50` meets the capacity condition above `linN`. -/
theorem gridCap_fifty {n : ℕ} (hn : linN ≤ n) : gridCap n 50 ≤ 5 * n := by
  unfold gridCap linN at *
  set j := Nat.log 2 n with hj
  have hj23 : 23 ≤ j := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  rw [← hj] at hlt
  have hpow := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  rw [← hj] at hpow
  -- `log₂ (100 n²) ≤ 2j + 8`
  have hlog : Nat.log 2 (2 * 50 * n ^ 2) ≤ 2 * j + 8 := by
    apply Nat.le_of_lt_succ
    apply Nat.log_lt_of_lt_pow (by positivity)
    have h2 : n ^ 2 < (2 ^ (j + 1)) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    calc 2 * 50 * n ^ 2 < 128 * (2 ^ (j + 1)) ^ 2 := by omega
      _ = 2 ^ (2 * j + 8 + 1) := by ring
  rcases (show j = 23 ∨ 24 ≤ j by omega) with h23 | h24
  · rw [h23] at hlog; omega
  · have h1 : ∀ i, 24 ≤ i → 760000 * (2 * i + 12) + 500 ≤ 5 * 2 ^ i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => norm_num
      | succ i hi ih => rw [pow_succ 2 i]; omega
    have := h1 j h24
    have : 304 * 50 ^ 2 * (Nat.log 2 (2 * 50 * n ^ 2) + 4) ≤ 760000 * (2 * j + 12) := by
      norm_num; omega
    omega

/-- The grid: the largest `m` with `gridCap n m ≤ 5n` and `64 m³ ≤ n`. -/
theorem exists_lin_width {n : ℕ} (hn : linN ≤ n) :
    ∃ m : ℕ, 50 ≤ m ∧ gridCap n m ≤ 5 * n ∧ 64 * m ^ 3 ≤ n ∧
      (5 * n < gridCap n (m + 1) ∨ n < 64 * (m + 1) ^ 3) := by
  classical
  let P : ℕ → Prop := fun m => gridCap n m ≤ 5 * n ∧ 64 * m ^ 3 ≤ n
  have hP50 : P 50 := ⟨gridCap_fifty hn, by unfold linN at hn; omega⟩
  have h50 : 50 ≤ n := by unfold linN at hn; omega
  set m := Nat.findGreatest P n
  have hm50 : 50 ≤ m := Nat.le_findGreatest h50 hP50
  have hPm : P m := Nat.findGreatest_spec h50 hP50
  refine ⟨m, hm50, hPm.1, hPm.2, ?_⟩
  by_contra hc
  push Not at hc
  have hle : m + 1 ≤ n := by
    calc m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      _ ≤ 64 * (m + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num)
      _ ≤ n := hc.2
  have := Nat.le_findGreatest (P := P) hle hc
  omega

/-- The hub algorithm on the grid, in natural numbers. -/
theorem optimalLength_le_lin_nat {n : ℕ} [NeZero n] (hn : linN ≤ n) (B : ReachableBoard n) :
    ∃ m : ℕ, 50 ≤ m ∧ 64 * m ^ 3 ≤ n ∧
      (5 * n < gridCap n (m + 1) ∨ n < 64 * (m + 1) ^ 3) ∧
      1000 * optimalLength B ≤ 1000 * manhattan B.val +
        2 * hubLinKX * (n ^ 2 * (n / (2 * m))) + 2 * hubLinKW * ((2 * m) ^ 2 * n ^ 2) +
        2000 * ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))) := by
  obtain ⟨m, hm50, hcap, hcube, hmax⟩ := exists_lin_width hn
  refine ⟨m, hm50, hcube, hmax, ?_⟩
  set k := 2 * m with hkdef
  set s := n / k with hsdef
  have hkpos : 0 < k := by omega
  have hmn : k * s ≤ n := Nat.mul_div_le n k
  have hmod : n % k + k * s = n := Nat.mod_add_div n k
  have hmodlt : n % k < k := Nat.mod_lt n hkpos
  -- `λ_A ≤ log₂ (k n²) + 4`
  have hs0 : 1 ≤ s := by
    have hkn : k ≤ n := by
      have : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
    exact Nat.div_pos hkn hkpos
  have hlamA : lamA k s ≤ Nat.log 2 (2 * m * n ^ 2) + 4 := by
    unfold lamA
    have : k ^ 3 * s ^ 2 ≤ 2 * m * n ^ 2 := by
      have h1 : (k * s) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn 2
      calc k ^ 3 * s ^ 2 = k * (k * s) ^ 2 := by ring
        _ ≤ k * n ^ 2 := Nat.mul_le_mul_left _ h1
        _ = 2 * m * n ^ 2 := by rw [hkdef]
    have := Nat.log_mono_right (b := 2) this
    omega
  -- capacity: `76 k λ_A ≤ 5 s`
  have hP1 : 76 * k * lamA k s ≤ 5 * s := by
    unfold gridCap at hcap
    set Λ := Nat.log 2 (2 * m * n ^ 2) + 4
    have h1 : 76 * k * lamA k s * k ≤ 304 * m ^ 2 * Λ := by
      calc 76 * k * lamA k s * k ≤ 76 * k * Λ * k := by gcongr
        _ = 304 * m ^ 2 * Λ := by rw [hkdef]; ring
    have h2 : 5 * n < 5 * (k * s) + 5 * k := by omega
    have h3 : 76 * k * lamA k s * k < 5 * s * k := by nlinarith
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right h3)
  have hroom : 4 * k + 4 ≤ s := by
    unfold gridCap at hcap
    have hΛ : 4 ≤ Nat.log 2 (2 * m * n ^ 2) + 4 := by omega
    have : 76 * k * 4 ≤ 5 * s := le_trans (by gcongr; unfold lamA; omega) hP1
    omega
  have hd : HDims (k * s) k s := ⟨by omega, ⟨m, by omega⟩, hroom, rfl⟩
  have hk100 : 100 ≤ k := by omega
  have hres := optimalLength_le_hub_residual B hd hk100 hP1
  simp only [← hsdef] at hres
  have hcapk : 729 * k ≤ s := by
    have := (capacity_lower_bounds hd hk100 hP1).2.1
    have : 76 * k * 48 ≤ 5 * s := le_trans (by gcongr) hP1
    omega
  have hbound := hubBound_le_lin hk100 hcapk
  have hX : (k * s) ^ 2 * s ≤ n ^ 2 * s := by gcongr
  have hW : k ^ 2 * (k * s) ^ 2 ≤ k ^ 2 * n ^ 2 := by gcongr
  have hx := Nat.mul_le_mul_left hubLinKX hX
  have hw := Nat.mul_le_mul_left hubLinKW hW
  nlinarith

end SlidingPuzzle.Hub
