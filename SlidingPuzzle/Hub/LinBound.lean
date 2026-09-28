import SlidingPuzzle.Hub.AsympBound

/-! # The hub algorithm without the logarithm: natural-number bounds

The in-flight budget is linear in `n` (`Rhub`), so the hub algorithm on side
`n = k*s` costs `O(n²s + k²n²)` (`hubBound_le_lin`) and `k ≍ n^(1/3)` gives
`O(n^(8/3))`. The capacity condition `76kλ_A ≤ 5s` still involves
`λ_A = log₂(k³s²) + 4 ≤ log₂(kn²) + 4`. Take `k = 2m` with `m` the largest
integer such that `304 m² Λ(m) + 10 m ≤ 5n`, `Λ(m) = log₂(2m n²) + 4`
(capacity), and `45 m³ ≤ n` (cube scale). For `n ≥ linN = 10⁹` the cube scale
is the binding one (`Hub/LinError.lean`).

For `n ≥ linN` this grid has `m ≥ 250` (`exists_lin_width`), and
`optimalLength_le_lin_nat` bounds the solution length by
`M + 2 (hubLinKX X + hubLinKW W)/1000 + 2 Z` with `X = n²s`, `W = k²n²` and `Z`
the prefix cost. -/
namespace SlidingPuzzle.Hub

open SlidingPuzzle

/-- The side from which the hub algorithm is used for the bound without the logarithm. -/
def linN : ℕ := 10 ^ 9

/-- The capacity term of the grid. -/
def gridCap (n m : ℕ) : ℕ := 304 * m ^ 2 * (Nat.log 2 (2 * m * n ^ 2) + 4) + 10 * m

/-- `M` meets the capacity condition from `N0` on, if it does so while the
logarithm is at most `T` and the square of the capacity term stays below
`25 · 2^L / (2M)` for larger logarithms `L`. -/
theorem gridCap_le_of {n M N0 : ℕ} (T : ℕ) (hn : N0 ≤ n) (hM : 1 ≤ M)
    (hbase : 304 * M ^ 2 * (T + 4) + 10 * M ≤ 5 * N0)
    (htail : 2 * M * (304 * M ^ 2 * (T + 5) + 10 * M) ^ 2 ≤ 25 * 2 ^ (T + 1)) :
    gridCap n M ≤ 5 * n := by
  unfold gridCap
  set L := Nat.log 2 (2 * M * n ^ 2) with hL
  rcases (show L ≤ T ∨ T + 1 ≤ L by omega) with hT | hT
  · have : 304 * M ^ 2 * (L + 4) ≤ 304 * M ^ 2 * (T + 4) := Nat.mul_le_mul_left _ (by omega)
    omega
  · -- `(capacity)² · 2M ≤ 25 · 2^L ≤ 25 · 2M n²`
    have hstep : ∀ i, T + 1 ≤ i → 2 * M * (304 * M ^ 2 * (i + 4) + 10 * M) ^ 2 ≤ 25 * 2 ^ i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => simpa [show T + 1 + 4 = T + 5 by ring] using htail
      | succ i hi ih =>
        set c := 304 * M ^ 2
        set A := c * (i + 4) + 10 * M
        have hA : c * 5 ≤ A := by
          have := Nat.mul_le_mul_left c (show 5 ≤ i + 4 by omega)
          omega
        have hA' : c * (i + 1 + 4) + 10 * M = A + c := by simp only [A]; ring
        rw [hA', pow_succ]
        have hsq : (A + c) ^ 2 ≤ 2 * A ^ 2 := by nlinarith
        calc 2 * M * (A + c) ^ 2 ≤ 2 * M * (2 * A ^ 2) := Nat.mul_le_mul_left _ hsq
          _ = 2 * (2 * M * A ^ 2) := by ring
          _ ≤ 2 * (25 * 2 ^ i) := Nat.mul_le_mul_left _ ih
          _ = 25 * (2 ^ i * 2) := by ring
    have h1 := hstep L hT
    have hpow : 2 ^ L ≤ 2 * M * n ^ 2 := Nat.pow_log_le_self 2 (by
      have : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hL; omega
        · exact h
      positivity)
    have h2 : 2 * M * (304 * M ^ 2 * (L + 4) + 10 * M) ^ 2 ≤ 2 * M * (5 * n) ^ 2 := by
      calc _ ≤ 25 * 2 ^ L := h1
        _ ≤ 25 * (2 * M * n ^ 2) := Nat.mul_le_mul_left _ hpow
        _ = 2 * M * (5 * n) ^ 2 := by ring
    have h3 := Nat.le_of_mul_le_mul_left h2 (by omega)
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3

/-- `m = 250` meets the capacity condition from `linN = 10⁹` on. -/
theorem gridCap_250 {n : ℕ} (hn : linN ≤ n) : gridCap n 250 ≤ 5 * n :=
  gridCap_le_of (N0 := 10 ^ 9) 64 hn (by norm_num) (by norm_num) (by norm_num)

/-- The grid: the largest `m` with `gridCap n m ≤ 5n` and `45 m³ ≤ n`. It is at
least `250`. -/
theorem exists_lin_width {n : ℕ} (hn : linN ≤ n) :
    ∃ m : ℕ, 250 ≤ m ∧ gridCap n m ≤ 5 * n ∧ 45 * m ^ 3 ≤ n ∧
      (5 * n < gridCap n (m + 1) ∨ n < 45 * (m + 1) ^ 3) := by
  classical
  let P : ℕ → Prop := fun m => gridCap n m ≤ 5 * n ∧ 45 * m ^ 3 ≤ n
  have hP : P 250 := ⟨gridCap_250 hn, by unfold linN at hn; omega⟩
  have h250 : 250 ≤ n := by unfold linN at hn; omega
  set m := Nat.findGreatest P n
  have hm : 250 ≤ m := Nat.le_findGreatest h250 hP
  have hPm : P m := Nat.findGreatest_spec (m := 250) h250 hP
  refine ⟨m, hm, hPm.1, hPm.2, ?_⟩
  by_contra hc
  push Not at hc
  have hle : m + 1 ≤ n := by
    calc m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      _ ≤ 45 * (m + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num)
      _ ≤ n := hc.2
  have := Nat.le_findGreatest (P := P) hle hc
  omega

/-- The hub algorithm on the grid, in natural numbers. -/
theorem optimalLength_le_lin_nat {n : ℕ} [NeZero n] (hn : linN ≤ n) (B : ReachableBoard n) :
    ∃ m : ℕ, 250 ≤ m ∧ 45 * m ^ 3 ≤ n ∧
      (5 * n < gridCap n (m + 1) ∨ n < 45 * (m + 1) ^ 3) ∧
      1000 * optimalLength B ≤ 1000 * manhattan B.val +
        2 * hubLinKX * (n ^ 2 * (n / (2 * m))) + 2 * hubLinKW * ((2 * m) ^ 2 * n ^ 2) +
        2000 * ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))) := by
  obtain ⟨m, hm, hcap, hcube, hmax⟩ := exists_lin_width hn
  refine ⟨m, hm, hcube, hmax, ?_⟩
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
  have hk500 : 500 ≤ k := by omega
  have hres := optimalLength_le_hub_residual B hd hk500 hP1
  simp only [← hsdef] at hres
  have hcapk : 881 * k ≤ s := by
    have := (capacity_lower_bounds hd hk500 hP1).2.1
    have : 76 * k * 58 ≤ 5 * s := le_trans (by gcongr) hP1
    omega
  have hbound := hubBound_le_lin hk500 hcapk
  have hX : (k * s) ^ 2 * s ≤ n ^ 2 * s := by gcongr
  have hW : k ^ 2 * (k * s) ^ 2 ≤ k ^ 2 * n ^ 2 := by gcongr
  have hx := Nat.mul_le_mul_left hubLinKX hX
  have hw := Nat.mul_le_mul_left hubLinKW hW
  nlinarith

end SlidingPuzzle.Hub
