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
      16 * GroupedOrder.lamN n * 73 ^ (2 * (h - 1)) ≤ n ∧
      (h = 2 → 16 * GroupedOrder.lamN n * (2 * GroupedOrder.lamN n - 1) ^ 2 ≤ n) := by
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
  -- depth `2`: branching `2λ - 1` fits one level
  have hone : h = 2 → 16 * lam * (2 * lam - 1) ^ 2 ≤ n := by
    intro h2
    have hnot : ¬ P (h - 1) := Nat.find_min hex (by omega)
    simp only [P, not_and, not_forall, not_le] at hnot
    obtain ⟨b, _, _, hfit, hbud⟩ := hnot (by omega)
    rw [h2] at hfit hbud
    have : 2 * lam - 1 ≤ b := by omega
    calc 16 * lam * (2 * lam - 1) ^ 2 ≤ 16 * lam * b ^ (2 * (2 - 1)) := by
          norm_num; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
      _ ≤ n := hfit
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
  refine ⟨h, b, j, hh1, ⟨t, by omega⟩, by omega, hjlt, hbud, hQj, ?_, hlow, hone⟩
  simpa [Q] using hQj1

/-- `n x² < 16 λ (K (x + 2))²` with `x ≥ 64`: the grid rounds by at most `33/32`. -/
theorem round_fine {n lam K x : ℕ} (hx : 64 ≤ x) (h : n * x ^ 2 < 16 * lam * (K * (x + 2)) ^ 2) :
    64 * n < 1089 * lam * K ^ 2 := by
  have h1 := Nat.mul_le_mul_right (65 * x + 64) hx
  have h2 : 1024 * (x + 2) ^ 2 ≤ 1089 * x ^ 2 := by nlinarith
  have h3 : 64 * (16 * lam * (K * (x + 2)) ^ 2) ≤ 1089 * lam * K ^ 2 * x ^ 2 := by
    have := Nat.mul_le_mul_left (lam * K ^ 2) h2
    calc 64 * (16 * lam * (K * (x + 2)) ^ 2) = lam * K ^ 2 * (1024 * (x + 2) ^ 2) := by ring
      _ ≤ lam * K ^ 2 * (1089 * x ^ 2) := this
      _ = _ := by ring
  have h4 : 64 * n * x ^ 2 < 1089 * lam * K ^ 2 * x ^ 2 := by
    calc 64 * n * x ^ 2 = 64 * (n * x ^ 2) := by ring
      _ < 64 * (16 * lam * (K * (x + 2)) ^ 2) := by linarith
      _ ≤ _ := h3
  exact Nat.lt_of_mul_lt_mul_right h4

/-- `λ` grows with the depth: `16 λ 73^(2m) ≤ n < 2^(λ/3)` gives `λ ≥ 33 + 36 m`. -/
theorem lam_depth {n m : ℕ} (hl : 64 ≤ GroupedOrder.lamN n)
    (h : 16 * GroupedOrder.lamN n * 73 ^ (2 * m) ≤ n) : 33 + 36 * m ≤ GroupedOrder.lamN n := by
  set E := Nat.log 2 n + 1 with hE
  have hnE : n < 2 ^ E := Nat.lt_pow_succ_log_self (by decide) n
  have hlam : GroupedOrder.lamN n = 3 * E := rfl
  have h1 : 2 ^ (10 + 12 * m) ≤ 16 * GroupedOrder.lamN n * 73 ^ (2 * m) := by
    have e : 2 ^ (10 + 12 * m) = 1024 * 4096 ^ m := by rw [pow_add, pow_mul]; norm_num
    have e2 : 73 ^ (2 * m) = 5329 ^ m := by rw [pow_mul]; norm_num
    rw [e, e2]
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by norm_num) m)
  have h2 : 2 ^ (10 + 12 * m) < 2 ^ E := lt_of_le_of_lt (h1.trans h) hnE
  have h3 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
  rw [hlam]; omega

theorem pow2_le73 : ∀ m : ℕ, 64 * 2 ^ (m + 2) ≤ 73 ^ (m + 2)
  | 0 => by norm_num
  | m + 1 => by
    have ih := pow2_le73 m
    rw [pow_succ, pow_succ 73]
    have : 73 ^ (m + 2) * 2 ≤ 73 ^ (m + 2) * 73 := Nat.mul_le_mul_left _ (by norm_num)
    calc 64 * (2 ^ (m + 2) * 2) = 64 * 2 ^ (m + 2) * 2 := by ring
      _ ≤ 73 ^ (m + 2) * 2 := Nat.mul_le_mul_right _ ih
      _ ≤ _ := this

open SlidingPuzzle in
/-- The tree bound for any branching within the lane budget `2λ`. -/
theorem optimalLength_le_budget {n h : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (B : ℕ → ℕ)
    (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 1 ≤ h) (hh4 : 4 * h ≤ GroupedOrder.lamN n)
    (hke : Even (HierMix.sz B h 0)) (hqe : Even (HierMix.nq B h))
    (hq : HierMix.nq B h ≤ 2 * GroupedOrder.lamN n) (hK : 64 ≤ HierMix.sz B h 0)
    (hlo : 16 * GroupedOrder.lamN n * HierMix.sz B h 0 ^ 2 ≤ n) (Bd : ReachableBoard n) :
    optimalLength Bd ≤ manhattan Bd.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * HierMix.sz B h 0) +
      2 * ((48 * h + 142) * HierMix.sz B h 0 ^ 2 * (n / HierMix.sz B h 0) ^ 3) := by
  have hl72 : 72 ≤ GroupedOrder.lamN n := lam_ge hn
  have hq2 : 2 ≤ HierMix.nq B h := by
    have e : HierMix.nq B h = ∑ ℓ ∈ range h, B ℓ := Fin.sum_univ_eq_sum_range B h
    rw [e]
    have := Finset.single_le_sum (f := B) (fun i _ => Nat.zero_le _)
      (mem_range.2 (show 0 < h by omega))
    exact le_trans (hB 0) this
  exact optimalLength_le_lanes_log (h := h) (HierMix.sys B h hB hh) rfl hke hqe hq2
    (HierMix.nq_le_sz hB) hK (by omega) hh4
    (by
      have := Nat.mul_le_mul_right (HierMix.sz B h 0 ^ 2) (Nat.mul_le_mul_left 8 hq)
      calc 8 * HierMix.sz B h 0 * HierMix.nq B h * HierMix.sz B h 0 =
            8 * HierMix.nq B h * HierMix.sz B h 0 ^ 2 := by ring
        _ ≤ 8 * (2 * GroupedOrder.lamN n) * HierMix.sz B h 0 ^ 2 := this
        _ = 16 * GroupedOrder.lamN n * HierMix.sz B h 0 ^ 2 := by ring
        _ ≤ n := hlo)
    (by
      calc 16 * HierMix.sz B h 0 * GroupedOrder.lamN n * HierMix.sz B h 0 =
            16 * GroupedOrder.lamN n * HierMix.sz B h 0 ^ 2 := by ring
        _ ≤ n := hlo) Bd

/-- The mixed grid on `m` levels, then one level of branching `d`. -/
def Bfree (c j d m : ℕ) (ℓ : ℕ) : ℕ := if ℓ < m then Bmix c j ℓ else d

theorem Bfree_ge {c j d m : ℕ} (hc : 2 ≤ c) (hd : 2 ≤ d) (ℓ : ℕ) : 2 ≤ Bfree c j d m ℓ := by
  unfold Bfree; split_ifs
  · exact Bmix_ge hc j ℓ
  · exact hd

theorem sz_Bfree {c j d m : ℕ} (hj : j ≤ m) :
    HierMix.sz (Bfree c j d m) (m + 1) 0 = (c + 2) ^ j * c ^ (m - j) * d := by
  unfold HierMix.sz
  rw [← range_eq_Ico, prod_range_succ]
  have e : ∏ ℓ ∈ range m, Bfree c j d m ℓ = ∏ ℓ ∈ range m, Bmix c j ℓ :=
    prod_congr rfl (fun ℓ hℓ => by unfold Bfree; rw [if_pos (mem_range.1 hℓ)])
  rw [e, prod_Bmix, min_eq_left hj]
  unfold Bfree; rw [if_neg (lt_irrefl m)]

theorem nq_Bfree {c j d m : ℕ} (hj : j ≤ m) :
    HierMix.nq (Bfree c j d m) (m + 1) = m * c + 2 * j + d := by
  rw [HierMix.nq, Fin.sum_univ_eq_sum_range (Bfree c j d m) (m + 1), sum_range_succ]
  have e : ∑ ℓ ∈ range m, Bfree c j d m ℓ = ∑ ℓ ∈ range m, Bmix c j ℓ :=
    sum_congr rfl (fun ℓ hℓ => by unfold Bfree; rw [if_pos (mem_range.1 hℓ)])
  rw [e, sum_Bmix, min_eq_left hj]
  unfold Bfree; rw [if_neg (lt_irrefl m)]

/-- With `c ≤ 62` and `d c < 64 (c + 2)`, the free level leaves room: `d + c ≤ 138`. -/
theorem free_room {c d : ℕ} (hc2 : 2 ≤ c) (hc : c ≤ 62) (hdc : d * c < 64 * (c + 2)) :
    d + c ≤ 138 := by
  by_contra h
  push Not at h
  have h1 : (139 - c) * c ≤ d * c := Nat.mul_le_mul_right _ (by omega)
  interval_cases c <;> omega

open SlidingPuzzle in
/-- The tree bound on a grid that rounds by at most `33/32`: `64 n < 1089 λ K²`. If the
branching `b` of `exists_lam_grid` is at least `64` the mixed grid does it. Otherwise the
depth is at least `2`, and the mixed grid of branching `c ≤ 62` on `h - 1` levels, sized for
`K / 64`, gets a last level of branching `d ≥ 64`; the budget `2λ ≥ 66 + 72(h-1)` holds
since `d c < 64(c + 2)`. -/
theorem optimalLength_le_fine {n : ℕ} [NeZero n] (hn : 2 ^ 23 ≤ n) (Bd : ReachableBoard n) :
    ∃ h K : ℕ, 1 ≤ h ∧ 16 * GroupedOrder.lamN n * 73 ^ (2 * (h - 1)) ≤ n ∧
      (h = 2 → 16 * GroupedOrder.lamN n * (2 * GroupedOrder.lamN n - 1) ^ 2 ≤ n) ∧ 64 ≤ K ∧
      16 * GroupedOrder.lamN n * K ^ 2 ≤ n ∧ 64 * n < 1089 * GroupedOrder.lamN n * K ^ 2 ∧
      optimalLength Bd ≤ manhattan Bd.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * K) +
        2 * ((48 * h + 142) * K ^ 2 * (n / K) ^ 3) := by
  obtain ⟨h, b, j, hh, hbe, hb8, hj, hbud, hlo, hhi, h73, htwo⟩ := exists_lam_grid hn
  set lam := GroupedOrder.lamN n with hlam
  have hl72 : 72 ≤ lam := lam_ge hn
  have hsmall : 102400 * lam ≤ n := lam_small hn
  have hh4 : 4 * h ≤ lam := by nlinarith
  by_cases hb64 : 64 ≤ b
  · -- the mixed grid rounds by `(b + 2)/b ≤ 33/32`
    set K := (b + 2) ^ j * b ^ (h - j) with hK
    have hround : n * b ^ 2 < 16 * lam * (K * (b + 2)) ^ 2 := by
      have e1 : (b + 2) ^ (j + 1) * b ^ (h - (j + 1)) * b = K * (b + 2) := by
        rw [hK]
        have : h - j = h - (j + 1) + 1 := by omega
        rw [this, pow_succ, pow_succ]; ring
      rw [← e1]
      have := Nat.mul_lt_mul_of_pos_right hhi (show 0 < b ^ 2 by positivity)
      calc n * b ^ 2 < _ := this
        _ = _ := by ring
    have hK64 : 64 ≤ K := by
      have h1 : 64 ≤ b ^ (h - j) := le_trans hb64 (Nat.le_self_pow (by omega) _)
      have h2 : 1 ≤ (b + 2) ^ j := Nat.one_le_pow _ _ (by omega)
      calc 64 = 1 * 64 := by norm_num
        _ ≤ K := Nat.mul_le_mul h2 h1
    have hb2 : 2 ≤ b := by omega
    have hsz := sz_Bmix (b := b) (h := h) hj.le
    have hnq := nq_Bmix (b := b) (h := h) hj.le
    have hres := optimalLength_le_budget hn (Bmix b j) (Bmix_ge hb2 j) hh hh4
      (by rw [hsz]; exact (hbe.pow_of_ne_zero (by omega)).mul_left _)
      (by rw [hnq]; obtain ⟨c, hc⟩ := hbe; exact ⟨h * c + j, by rw [hc]; ring⟩)
      (by rw [hnq]; nlinarith) (by rw [hsz]; exact hK64) (by rw [hsz]; exact hlo) Bd
    rw [hsz] at hres
    exact ⟨h, K, hh, h73, htwo, hK64, hlo, round_fine hb64 hround, hres⟩
  · push Not at hb64
    have hb62 : b ≤ 62 := by obtain ⟨r, hr⟩ := hbe; omega
    -- the grid of branching `b < 64` is below `64^h`
    have hup : n < 16 * lam * (64 ^ h) ^ 2 := by
      have h1 : (b + 2) ^ (j + 1) * b ^ (h - (j + 1)) ≤ 64 ^ (j + 1) * 64 ^ (h - (j + 1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _)
      rw [← pow_add, show j + 1 + (h - (j + 1)) = h by omega] at h1
      exact lt_of_lt_of_le hhi (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2))
    -- so the depth is at least `2`
    obtain ⟨m, rfl⟩ : ∃ m, h = m + 2 := by
      refine ⟨h - 2, ?_⟩
      by_contra hc
      have h1 : h = 1 := by omega
      rw [h1] at hup
      nlinarith
    have hm1 : m + 2 - 1 = m + 1 := by omega
    rw [hm1] at h73
    have hlamd := lam_depth (m := m + 1) (by omega) h73
    -- lowest branching `c` of the `m + 1` upper levels, sized for `K / 64`
    let Pc : ℕ → Prop := fun t => 16 * lam * (64 * (2 * t) ^ (m + 1)) ^ 2 ≤ n
    have hPc1 : Pc 1 := by
      show 16 * lam * (64 * (2 * 1) ^ (m + 1)) ^ 2 ≤ n
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        have h2 := htwo rfl
        have : 128 ≤ 2 * lam - 1 := by omega
        calc 16 * lam * (64 * (2 * 1) ^ (0 + 1)) ^ 2 = 16 * lam * 128 ^ 2 := by norm_num
          _ ≤ 16 * lam * (2 * lam - 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
          _ ≤ n := h2
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h1 := pow2_le73 m'
        have h2 : (64 * 2 ^ (m' + 2)) ^ 2 ≤ 73 ^ (2 * (m' + 1 + 1)) := by
          rw [show 2 * (m' + 1 + 1) = (m' + 2) * 2 by ring, pow_mul]
          exact Nat.pow_le_pow_left h1 2
        calc 16 * lam * (64 * (2 * 1) ^ (m' + 1 + 1)) ^ 2 =
              16 * lam * (64 * 2 ^ (m' + 2)) ^ 2 := by norm_num
          _ ≤ 16 * lam * 73 ^ (2 * (m' + 1 + 1)) := Nat.mul_le_mul_left _ h2
          _ ≤ n := h73
    set t := Nat.findGreatest Pc n with ht
    have hPt : Pc t := Nat.findGreatest_spec (P := Pc) (by omega) hPc1
    have ht1 : 1 ≤ t := Nat.le_findGreatest (by omega) hPc1
    have htn : t < n := by
      have h1 : 2 * t ≤ (2 * t) ^ (m + 1) := Nat.le_self_pow (by omega) _
      have h2 : (2 * t) ^ (m + 1) ≤ (64 * (2 * t) ^ (m + 1)) ^ 2 := by nlinarith
      have h3 : (64 * (2 * t) ^ (m + 1)) ^ 2 ≤ 16 * lam * (64 * (2 * t) ^ (m + 1)) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by omega)
      have : 16 * lam * (64 * (2 * t) ^ (m + 1)) ^ 2 ≤ n := hPt
      omega
    have hnPt : ¬ Pc (t + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self t) (by omega)
    set c := 2 * t with hc
    have hc2 : 2 ≤ c := by omega
    -- `c ≤ 62`, as `c ≥ 64` would give `64^(m+2)` below `K`
    have hc62 : c ≤ 62 := by
      by_contra hcc
      push Not at hcc
      have h1 : 64 * 64 ^ (m + 1) ≤ 64 * c ^ (m + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have h2 : 16 * lam * (64 ^ (m + 2)) ^ 2 ≤ n := by
        rw [show 64 ^ (m + 2) = 64 * 64 ^ (m + 1) by ring]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)) hPt
      omega
    -- the mixed grid of `c` and `c + 2` on the upper levels
    let Q : ℕ → Prop := fun i => 16 * lam * (64 * ((c + 2) ^ i * c ^ (m + 1 - i))) ^ 2 ≤ n
    set i := Nat.findGreatest Q (m + 1) with hi
    have hQ0 : Q 0 := by
      show 16 * lam * (64 * ((c + 2) ^ 0 * c ^ (m + 1 - 0))) ^ 2 ≤ n
      rw [Nat.sub_zero, pow_zero, one_mul]; exact hPt
    have hQi : Q i := Nat.findGreatest_spec (P := Q) (Nat.zero_le _) hQ0
    have him : i ≤ m + 1 := Nat.findGreatest_le _
    have hQm : ¬ Q (m + 1) := by
      show ¬ 16 * lam * (64 * ((c + 2) ^ (m + 1) * c ^ (m + 1 - (m + 1)))) ^ 2 ≤ n
      rw [Nat.sub_self, pow_zero, mul_one, hc, show 2 * t + 2 = 2 * (t + 1) by ring]
      exact hnPt
    have hilt : i < m + 1 := by
      rcases Nat.lt_or_ge i (m + 1) with h1 | h1
      · exact h1
      · exact absurd (show i = m + 1 by omega ▸ hQi) hQm
    have hQi1 : ¬ Q (i + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self i) (by omega)
    set P := (c + 2) ^ i * c ^ (m + 1 - i) with hP
    have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hnc : n * c ^ 2 < 16 * lam * (64 * P * (c + 2)) ^ 2 := by
      have e1 : (c + 2) ^ (i + 1) * c ^ (m + 1 - (i + 1)) * c = P * (c + 2) := by
        rw [hP]
        have : m + 1 - i = m + 1 - (i + 1) + 1 := by omega
        rw [this, pow_succ, pow_succ]; ring
      have h1 : n < 16 * lam * (64 * ((c + 2) ^ (i + 1) * c ^ (m + 1 - (i + 1)))) ^ 2 := by
        simpa [Q] using hQi1
      have := Nat.mul_lt_mul_of_pos_right h1 (show 0 < c ^ 2 by positivity)
      calc n * c ^ 2 < _ := this
        _ = 16 * lam * (64 * ((c + 2) ^ (i + 1) * c ^ (m + 1 - (i + 1)) * c)) ^ 2 := by ring
        _ = _ := by rw [e1]; ring
    -- the free level: the largest even `d` with `16 λ (P d)² ≤ n`
    let R : ℕ → Prop := fun u => 16 * lam * (P * (2 * u)) ^ 2 ≤ n
    have hR32 : R 32 := by
      show 16 * lam * (P * (2 * 32)) ^ 2 ≤ n
      have : 16 * lam * (64 * P) ^ 2 ≤ n := hQi
      calc 16 * lam * (P * (2 * 32)) ^ 2 = 16 * lam * (64 * P) ^ 2 := by ring
        _ ≤ n := this
    set u := Nat.findGreatest R n with hu
    have hRu : R u := Nat.findGreatest_spec (P := R) (by omega) hR32
    have hu32 : 32 ≤ u := Nat.le_findGreatest (by omega) hR32
    have hun : u < n := by
      have h1 : 2 * u ≤ P * (2 * u) := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : P * (2 * u) ≤ (P * (2 * u)) ^ 2 := Nat.le_self_pow (by norm_num) _
      have h3 : (P * (2 * u)) ^ 2 ≤ 16 * lam * (P * (2 * u)) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by omega)
      have : 16 * lam * (P * (2 * u)) ^ 2 ≤ n := hRu
      omega
    have hnRu : ¬ R (u + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self u) (by omega)
    set d := 2 * u with hd
    have hd64 : 64 ≤ d := by omega
    set K := P * d with hK
    have hlo' : 16 * lam * K ^ 2 ≤ n := hRu
    have hround : n * d ^ 2 < 16 * lam * (K * (d + 2)) ^ 2 := by
      have h1 : n < 16 * lam * (P * (d + 2)) ^ 2 := by
        have : ¬ 16 * lam * (P * (2 * (u + 1))) ^ 2 ≤ n := hnRu
        rw [show 2 * (u + 1) = d + 2 by omega] at this
        omega
      have := Nat.mul_lt_mul_of_pos_right h1 (show 0 < d ^ 2 by positivity)
      calc n * d ^ 2 < _ := this
        _ = _ := by rw [hK]; ring
    -- the budget: `d c < 64 (c + 2)`
    have hdc : d * c < 64 * (c + 2) := by
      have h1 : 16 * lam * (P * d) ^ 2 * c ^ 2 ≤ n * c ^ 2 := Nat.mul_le_mul_right _ hlo'
      have h2 : 16 * lam * ((P * d * c) ^ 2) < 16 * lam * ((P * (64 * (c + 2))) ^ 2) := by
        calc 16 * lam * ((P * d * c) ^ 2) = 16 * lam * (P * d) ^ 2 * c ^ 2 := by ring
          _ ≤ n * c ^ 2 := h1
          _ < 16 * lam * (64 * P * (c + 2)) ^ 2 := hnc
          _ = _ := by ring
      have h3 : (P * d * c) ^ 2 < (P * (64 * (c + 2))) ^ 2 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : P * d * c < P * (64 * (c + 2)) := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
      rw [mul_assoc] at h4
      exact Nat.lt_of_mul_lt_mul_left h4
    have hroom := free_room hc2 hc62 hdc
    have hmc : m * c ≤ m * 62 := Nat.mul_le_mul_left m hc62
    have hbudget : (m + 1) * c + 2 * i + d ≤ 2 * lam := by
      have e : (m + 1) * c = m * c + c := by ring
      rw [e]
      have : i ≤ m := by omega
      linarith
    have hsz := sz_Bfree (c := c) (j := i) (d := d) (m := m + 1) him
    have hnq := nq_Bfree (c := c) (j := i) (d := d) (m := m + 1) him
    have hK64 : 64 ≤ K := le_trans hd64 (Nat.le_mul_of_pos_left _ (by omega))
    have hres := optimalLength_le_budget hn (Bfree c i d (m + 1)) (Bfree_ge hc2 (by omega))
      (by omega) hh4
      (by rw [hsz]; exact ⟨P * u, by rw [hP, hd]; ring⟩)
      (by rw [hnq]; exact ⟨(m + 1) * t + i + u, by rw [hc, hd]; ring⟩)
      (by rw [hnq]; exact hbudget)
      (by rw [hsz]; exact hK64) (by rw [hsz]; exact hlo') Bd
    rw [hsz] at hres
    refine ⟨m + 2, K, by omega, by rw [hm1]; exact h73, htwo, hK64, hlo',
      round_fine hd64 hround, ?_⟩
    simpa [hP, hK] using hres

end SlidingPuzzle.Tree
