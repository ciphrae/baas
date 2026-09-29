import SlidingPuzzle.Tree.FinalLog
import SlidingPuzzle.Tree.MixGrid

/-! # Lane width against the logarithmic slack: error `117 n^(5/2) (ln n)^(3/2)`

With `λ = 3(⌊log₂ n⌋ + 1)`, the run needs `16k²λ ≤ n` (residence windows) and
`8k²q ≤ n` (lane width). So `k ≈ √(n/16λ)` whatever the depth, and the lanes are free as
long as `q ≤ 2λ`. The depth is the smallest `h` whose branching fits this budget: with
`b_h` the largest even `b` with `16λ b^(2h) ≤ n`, the smallest `h` with `h(b_h + 2) ≤ 2λ`.

Minimality makes the branching of the previous depth large: `(h-1)(b + 2) > 2λ` and
`b^(2(h-1)) ≤ n < 2^(λ/3)` give `b^12 < 2^(b+2)`, so `b ≥ 73`. Hence
`73^(2(h-1)) ≤ n` and `b_h ≥ 8`, and on the mixed grid `n < 25λk²`. The cost
`2(48h + 142) n³/k ≤ 10(48h + 142)√λ n^(5/2)` is then
`(117 ln n + 4100) √(ln n) n^(5/2)` for `n ≥ 2²³`. -/
namespace SlidingPuzzle.Tree

open Finset

theorem pow_ge_linear : ∀ E : ℕ, 23 ≤ E → 307200 * (E + 1) ≤ 2 ^ E
  | 23, _ => by norm_num
  | E + 24, _ => by
    have ih := pow_ge_linear (E + 23) (by omega)
    rw [pow_succ]
    omega

/-- `λ` is tiny against `n ≥ 2²³`. -/
theorem lam_small {n : ℕ} (hn : 2 ^ 23 ≤ n) : 102400 * GroupedOrder.lamN n ≤ n := by
  have hE : 23 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have h1 := pow_ge_linear _ hE
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  unfold GroupedOrder.lamN
  omega

theorem lam_ge {n : ℕ} (hn : 2 ^ 23 ≤ n) : 72 ≤ GroupedOrder.lamN n := by
  have := lamN_ge_of_pow hn
  omega

/-- `b^12 ≥ 2^(b+2)` for `2 ≤ b ≤ 72`. -/
theorem pow12_lt {b : ℕ} (h2 : 2 ≤ b) (h : b ^ 12 < 2 ^ (b + 2)) : 73 ≤ b := by
  by_contra hc
  push Not at hc
  interval_cases b <;> norm_num at h

/-- A depth whose branching overflows the lane budget has branching at least `73`. -/
theorem branch_large {n m b : ℕ} (hm : 1 ≤ m) (hb : 2 ≤ b)
    (hfit : 16 * GroupedOrder.lamN n * b ^ (2 * m) ≤ n)
    (hbud : 2 * GroupedOrder.lamN n < m * (b + 2)) : 73 ≤ b := by
  apply pow12_lt hb
  set E := Nat.log 2 n + 1 with hE
  have hnE : n < 2 ^ E := Nat.lt_pow_succ_log_self (by decide) n
  have hlam : GroupedOrder.lamN n = 3 * E := rfl
  have hb1 : b ^ (2 * m) ≤ n := by
    have : 1 ≤ 16 * GroupedOrder.lamN n := by rw [hlam]; omega
    calc b ^ (2 * m) = 1 * b ^ (2 * m) := (one_mul _).symm
      _ ≤ 16 * GroupedOrder.lamN n * b ^ (2 * m) := Nat.mul_le_mul_right _ this
      _ ≤ n := hfit
  have h1 : b ^ (2 * m) < 2 ^ E := lt_of_le_of_lt hb1 hnE
  have h2 : (b ^ 12) ^ m < (2 ^ (b + 2)) ^ m := by
    calc (b ^ 12) ^ m = (b ^ (2 * m)) ^ 6 := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ < (2 ^ E) ^ 6 := Nat.pow_lt_pow_left h1 (by norm_num)
      _ = 2 ^ (6 * E) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (m * (b + 2)) := Nat.pow_le_pow_right (by norm_num) (by rw [hlam] at hbud; omega)
      _ = (2 ^ (b + 2)) ^ m := by rw [← pow_mul]; ring_nf
  exact (Nat.pow_lt_pow_iff_left (by omega : m ≠ 0)).1 h2

theorem pow64_le : ∀ m : ℕ, 64 ^ (m + 2) ≤ 5329 ^ (m + 1)
  | 0 => by norm_num
  | m + 1 => by
    have ih := pow64_le m
    rw [pow_succ, pow_succ 5329]
    have : 64 ^ (m + 2) * 64 ≤ 5329 ^ (m + 1) * 64 := Nat.mul_le_mul_right _ ih
    have : 5329 ^ (m + 1) * 64 ≤ 5329 ^ (m + 1) * 5329 := Nat.mul_le_mul_left _ (by norm_num)
    omega

/-- The grid: the smallest depth whose largest even branching fits the lane budget `2λ`,
then the mixed grid below `16λ k² ≤ n`. -/
theorem exists_lam_grid {n : ℕ} (hn : 2 ^ 23 ≤ n) :
    ∃ h b j, 1 ≤ h ∧ Even b ∧ 8 ≤ b ∧ j < h ∧ h * (b + 2) ≤ 2 * GroupedOrder.lamN n ∧
      16 * GroupedOrder.lamN n * ((b + 2) ^ j * b ^ (h - j)) ^ 2 ≤ n ∧
      n < 16 * GroupedOrder.lamN n * ((b + 2) ^ (j + 1) * b ^ (h - (j + 1))) ^ 2 ∧
      73 ^ (2 * (h - 1)) ≤ n := by
  classical
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hsmall : 102400 * lam ≤ n := lam_small hn
  let P : ℕ → Prop := fun h =>
    1 ≤ h ∧ ∀ b ≤ n, 2 ≤ b → 16 * lam * b ^ (2 * h) ≤ n → h * (b + 2) ≤ 2 * lam
  have hex : ∃ h, P h := by
    refine ⟨n, by omega, fun b _ hb hfit => ?_⟩
    exfalso
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ b ^ (2 * n) :=
      calc 2 ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ b ^ (2 * n) := Nat.pow_le_pow_left hb _
    have h3 : b ^ (2 * n) ≤ 16 * lam * b ^ (2 * n) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  set h := Nat.find hex with hh
  have hP : P h := Nat.find_spec hex
  have hh1 : 1 ≤ h := hP.1
  -- the previous depth overflows, so its branching is at least `73`
  have hlow : 16 * lam * 73 ^ (2 * (h - 1)) ≤ n := by
    rcases Nat.eq_or_lt_of_le hh1 with h1 | h1
    · rw [← h1]; simp; omega
    · have hnot : ¬ P (h - 1) := Nat.find_min hex (by omega)
      simp only [P, not_and, not_forall, not_le] at hnot
      obtain ⟨b, _, hb2, hfit, hbud⟩ := hnot (by omega)
      have h73 := branch_large (m := h - 1) (by omega) hb2 hfit hbud
      calc 16 * lam * 73 ^ (2 * (h - 1)) ≤ 16 * lam * b ^ (2 * (h - 1)) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h73 _)
        _ ≤ n := hfit
  have h73n : 73 ^ (2 * (h - 1)) ≤ n :=
    le_trans (Nat.le_mul_of_pos_left _ (by omega)) hlow
  -- branching `8` fits at depth `h`
  have h8 : 16 * lam * (2 * 4) ^ (2 * h) ≤ n := by
    rcases Nat.eq_or_lt_of_le hh1 with h1 | h1
    · rw [← h1]; norm_num; omega
    · obtain ⟨m, hm⟩ : ∃ m, h = m + 2 := ⟨h - 2, by omega⟩
      have e1 : (2 * 4) ^ (2 * h) = 64 ^ (m + 2) := by rw [hm, pow_mul]; norm_num
      have e2 : 73 ^ (2 * (h - 1)) = 5329 ^ (m + 1) := by
        rw [hm, show m + 2 - 1 = m + 1 by omega, pow_mul]; norm_num
      rw [e1]; rw [e2] at hlow
      exact le_trans (Nat.mul_le_mul_left _ (pow64_le m)) hlow
  -- the largest even branching at depth `h`
  set t := Nat.findGreatest (fun t => 16 * lam * (2 * t) ^ (2 * h) ≤ n) n with ht
  have ht4 : 4 ≤ t := Nat.le_findGreatest (by omega) h8
  have hPt : 16 * lam * (2 * t) ^ (2 * h) ≤ n :=
    Nat.findGreatest_spec (P := fun t => 16 * lam * (2 * t) ^ (2 * h) ≤ n) (by omega) h8
  have htn : 2 * t ≤ n := by
    have : 2 * t ≤ (2 * t) ^ (2 * h) := Nat.le_self_pow (by omega) _
    have : (2 * t) ^ (2 * h) ≤ 16 * lam * (2 * t) ^ (2 * h) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnt : n < 16 * lam * (2 * (t + 1)) ^ (2 * h) := by
    have := Nat.findGreatest_is_greatest (P := fun t => 16 * lam * (2 * t) ^ (2 * h) ≤ n)
      (Nat.lt_succ_self t) (by omega)
    simpa using this
  set b := 2 * t with hb
  have hb2 : 2 * (t + 1) = b + 2 := by omega
  rw [hb2] at hnt
  have hbud : h * (b + 2) ≤ 2 * lam := hP.2 b htn (by omega) hPt
  -- the mixed grid
  let Q : ℕ → Prop := fun j => 16 * lam * ((b + 2) ^ j * b ^ (h - j)) ^ 2 ≤ n
  set j := Nat.findGreatest Q h with hj
  have hQ0 : Q 0 := by
    show 16 * lam * ((b + 2) ^ 0 * b ^ (h - 0)) ^ 2 ≤ n
    rw [Nat.sub_zero, pow_zero, one_mul, ← pow_mul, mul_comm h 2]; exact hPt
  have hQj : Q j := Nat.findGreatest_spec (P := Q) (Nat.zero_le h) hQ0
  have hjh : j ≤ h := Nat.findGreatest_le h
  have hQh : ¬ Q h := by
    show ¬ 16 * lam * ((b + 2) ^ h * b ^ (h - h)) ^ 2 ≤ n
    rw [Nat.sub_self, pow_zero, mul_one, ← pow_mul, mul_comm h 2]; omega
  have hjlt : j < h := by
    rcases Nat.lt_or_ge j h with h1 | h1
    · exact h1
    · exact absurd (show j = h by omega ▸ hQj) hQh
  have hQj1 : ¬ Q (j + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self j) (by omega)
  refine ⟨h, b, j, hh1, ⟨t, by omega⟩, by omega, hjlt, hbud, hQj, ?_, h73n⟩
  simpa [Q] using hQj1

open SlidingPuzzle in
/-- The tree bound on the grid of `exists_lam_grid`, in integers. -/
theorem optimalLength_le_lam {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ReachableBoard n) :
    ∃ h K : ℕ, 1 ≤ h ∧ 73 ^ (2 * (h - 1)) ≤ n ∧ 64 ≤ K ∧
      16 * GroupedOrder.lamN n * K ^ 2 ≤ n ∧ n < 25 * GroupedOrder.lamN n * K ^ 2 ∧
      optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * K) +
        2 * ((48 * h + 142) * K ^ 2 * (n / K) ^ 3) := by
  obtain ⟨h, b, j, hh, hbe, hb8, hj, hbud, hlo, hhi, h73⟩ := exists_lam_grid hn
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hsmall : 102400 * lam ≤ n := lam_small hn
  set K := (b + 2) ^ j * b ^ (h - j) with hK
  -- one more step of the grid fails: `n < 25 λ K²`
  have hhi' : n < 25 * lam * K ^ 2 := by
    have e1 : (b + 2) ^ (j + 1) * b ^ (h - (j + 1)) * b = K * (b + 2) := by
      rw [hK]
      have : h - j = h - (j + 1) + 1 := by omega
      rw [this, pow_succ, pow_succ]; ring
    have h1 : n * b ^ 2 < 16 * lam * (K * (b + 2)) ^ 2 := by
      rw [← e1]
      have := Nat.mul_lt_mul_of_pos_right hhi (show 0 < b ^ 2 by positivity)
      calc n * b ^ 2 < _ := this
        _ = _ := by ring
    have h2 : 16 * (b + 2) ^ 2 ≤ 25 * b ^ 2 := by nlinarith
    have h3 : 16 * lam * (K * (b + 2)) ^ 2 * 16 ≤ 25 * lam * K ^ 2 * 16 * b ^ 2 := by
      have := Nat.mul_le_mul_left (16 * lam * K ^ 2) h2
      calc 16 * lam * (K * (b + 2)) ^ 2 * 16 = 16 * lam * K ^ 2 * (16 * (b + 2) ^ 2) := by ring
        _ ≤ 16 * lam * K ^ 2 * (25 * b ^ 2) := this
        _ = _ := by ring
    have h4 : n * 16 * b ^ 2 < 25 * lam * K ^ 2 * 16 * b ^ 2 := by nlinarith
    have h5 : n * 16 < 25 * lam * K ^ 2 * 16 := Nat.lt_of_mul_lt_mul_right h4
    omega
  -- `K ≥ 64` from `n ≥ 102400 λ`
  have hK64 : 64 ≤ K := by
    by_contra hc
    push Not at hc
    have : K ^ 2 ≤ 63 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : 25 * lam * K ^ 2 ≤ 25 * lam * 63 ^ 2 := Nat.mul_le_mul_left _ this
    omega
  -- the lane system
  have hb2 : 2 ≤ b := by omega
  have hB := Bmix_ge hb2 j
  have hsz := sz_Bmix (b := b) (h := h) hj.le
  have hnq := nq_Bmix (b := b) (h := h) hj.le
  have hqk := HierMix.nq_le_sz (B := Bmix b j) (h := h) hB
  rw [hsz, hnq] at hqk
  have hq : h * b + 2 * j ≤ 2 * lam := by nlinarith
  have hres := optimalLength_le_lanes_log (h := h) (HierMix.sys (Bmix b j) h hB hh) rfl
    (by rw [hsz]; exact (hbe.pow_of_ne_zero (by omega)).mul_left _)
    (by rw [hnq]; obtain ⟨c, hc⟩ := hbe; exact ⟨h * c + j, by rw [hc]; ring⟩)
    (by rw [hnq]; nlinarith)
    (by rw [hsz, hnq]; exact hqk) (by rw [hsz]; exact hK64) (by omega) (by nlinarith)
    (by
      rw [hsz, hnq]
      have := Nat.mul_le_mul_right (K ^ 2) (Nat.mul_le_mul_left 8 hq)
      calc 8 * K * (h * b + 2 * j) * K = 8 * (h * b + 2 * j) * K ^ 2 := by ring
        _ ≤ 8 * (2 * lam) * K ^ 2 := this
        _ = 16 * lam * K ^ 2 := by ring
        _ ≤ n := hlo)
    (by
      rw [hsz]
      calc 16 * K * lam * K = 16 * lam * K ^ 2 := by ring
        _ ≤ n := hlo) B
  rw [hsz] at hres
  exact ⟨h, K, hh, h73, hK64, hlo, hhi', hres⟩

end SlidingPuzzle.Tree
