import SlidingPuzzle.Hub.AsympBound

/-! # The hub algorithm without the logarithm: natural-number bounds

The in-flight budget is linear in `n` (`Rhub`), so the hub algorithm on side
`n = k*s` costs `O(n²s + k²n²)` (`hubBound_le_lin`) and `k ≍ n^(1/3)` gives
`O(n^(8/3))`. The capacity condition `48kL ≤ s` still involves `L = log₂ n + 1`;
for moderate `n` it limits `k`. Take `k = 2m` with `m` the largest integer such
that `192 m² L ≤ n` (capacity) and `64 m³ ≤ n` (cube scale).

For `n ≥ linN = 11·2^20` this grid has `m ≥ 50` (`exists_lin_width`), and
`optimalLength_le_lin_nat` bounds the solution length by
`M + 2 (hubLinKX X + hubLinKW W)/1000 + 2 Z` with `X = n²s`, `W = k²n²` and `Z`
the prefix cost. -/
namespace SlidingPuzzle.Hub

open SlidingPuzzle

/-- The side from which the hub algorithm is used for the bound without the logarithm. -/
def linN : ℕ := 11 * 2 ^ 20

/-- Above `linN`, the logarithm is small against `n`: `480000 L ≤ n` and
`125 (192 L)³ ≤ 1061208 n`, that is `192 L ≤ (102/5) n^(1/3)`. -/
theorem lin_log_bounds {n : ℕ} (hn : linN ≤ n) :
    480000 * (Nat.log 2 n + 1) ≤ n ∧ 125 * (192 * (Nat.log 2 n + 1)) ^ 3 ≤ 1061208 * n := by
  unfold linN at hn
  have hj : 23 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hpow := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  rcases (show Nat.log 2 n = 23 ∨ 24 ≤ Nat.log 2 n by omega) with h23 | h24
  · rw [h23]; constructor <;> norm_num <;> omega
  · set j := Nat.log 2 n
    have h1 : ∀ i, 24 ≤ i → 480000 * (i + 1) ≤ 2 ^ i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => norm_num
      | succ i hi ih => rw [pow_succ 2 i]; omega
    have h2 : ∀ i, 24 ≤ i → 125 * (192 * (i + 1)) ^ 3 ≤ 1061208 * 2 ^ i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => norm_num
      | succ i hi ih =>
        have hstep : 125 * (192 * (i + 1 + 1)) ^ 3 ≤ 2 * (125 * (192 * (i + 1)) ^ 3) := by
          obtain ⟨t, rfl⟩ : ∃ t, i = t + 24 := ⟨i - 24, by omega⟩
          ring_nf
          nlinarith [Nat.zero_le t, Nat.zero_le (t ^ 2), Nat.zero_le (t ^ 3)]
        rw [pow_succ 2 i]; omega
    exact ⟨(h1 j h24).trans hpow, (h2 j h24).trans (Nat.mul_le_mul_left _ hpow)⟩

/-- The grid: the largest `m` with `192 m² L ≤ n` and `64 m³ ≤ n`. -/
theorem exists_lin_width {n : ℕ} (hn : linN ≤ n) :
    ∃ m : ℕ, 50 ≤ m ∧ 192 * m ^ 2 * (Nat.log 2 n + 1) ≤ n ∧ 64 * m ^ 3 ≤ n ∧
      (n < 192 * (m + 1) ^ 2 * (Nat.log 2 n + 1) ∨ n < 64 * (m + 1) ^ 3) := by
  classical
  set L := Nat.log 2 n + 1
  let P : ℕ → Prop := fun m => 192 * m ^ 2 * L ≤ n ∧ 64 * m ^ 3 ≤ n
  have hlog := (lin_log_bounds hn).1
  have hP50 : P 50 := by
    constructor
    · omega
    · unfold linN at hn; omega
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
    ∃ m : ℕ, 50 ≤ m ∧ 192 * m ^ 2 * (Nat.log 2 n + 1) ≤ n ∧ 64 * m ^ 3 ≤ n ∧
      (n < 192 * (m + 1) ^ 2 * (Nat.log 2 n + 1) ∨ n < 64 * (m + 1) ^ 3) ∧
      1000 * optimalLength B ≤ 1000 * manhattan B.val +
        2 * hubLinKX * (n ^ 2 * (n / (2 * m))) + 2 * hubLinKW * ((2 * m) ^ 2 * n ^ 2) +
        2000 * ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))) := by
  obtain ⟨m, hm50, hcap, hcube, hmax⟩ := exists_lin_width hn
  refine ⟨m, hm50, hcap, hcube, hmax, ?_⟩
  set L := Nat.log 2 n + 1 with hLdef
  set k := 2 * m with hkdef
  set s := n / k with hsdef
  have hkpos : 0 < k := by omega
  have hL : 1 ≤ L := by omega
  -- capacity, room and `8k² ≤ s`
  have hks2 : 8 * k ^ 2 ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    rw [hkdef]; nlinarith only [hcube]
  have hroom : 4 * k + 4 ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    have : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) _
    have : m ^ 2 ≤ m ^ 2 * L := Nat.le_mul_of_pos_right _ hL
    rw [hkdef]
    nlinarith
  have hmn : k * s ≤ n := Nat.mul_div_le n k
  have hd : HDims (k * s) k s := ⟨by omega, ⟨m, by omega⟩, hroom, rfl⟩
  have hlogks : Nat.log 2 (k * s) ≤ Nat.log 2 n := Nat.log_mono_right hmn
  have hP1 : 48 * k * (Nat.log 2 (k * s) + 1) ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    calc 48 * k * (Nat.log 2 (k * s) + 1) * k ≤ 48 * k * L * k := by gcongr; omega
      _ = 192 * m ^ 2 * L := by rw [hkdef]; ring
      _ ≤ n := hcap
  have hres := optimalLength_le_hub_residual B hd hP1 hks2
  simp only [← hsdef] at hres
  -- the residual side is at least `2^23`
  have hreslarge : 2 ^ 23 ≤ k * s := by
    have hmod := Nat.mod_lt n hkpos
    have heq := Nat.mod_add_div n k
    change n % k + k * s = n at heq
    have hkk : k * k ≤ k * s := Nat.mul_le_mul_left k (by omega)
    unfold linN at hn
    by_contra hlt
    have hk13 : k < 2 ^ 12 := by
      by_contra hk'
      have := Nat.mul_le_mul (not_lt.mp hk') (not_lt.mp hk')
      omega
    omega
  have hL24 : 24 ≤ Nat.log 2 (k * s) + 1 := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hreslarge
    omega
  have hbound := hubBound_le_lin (show 100 ≤ k by omega) hL24 hP1
  have hX : (k * s) ^ 2 * s ≤ n ^ 2 * s := by gcongr
  have hW : k ^ 2 * (k * s) ^ 2 ≤ k ^ 2 * n ^ 2 := by gcongr
  have hx := Nat.mul_le_mul_left hubLinKX hX
  have hw := Nat.mul_le_mul_left hubLinKW hW
  nlinarith

end SlidingPuzzle.Hub
