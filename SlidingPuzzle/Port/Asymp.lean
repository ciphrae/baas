import SlidingPuzzle.Port.Lanes
import SlidingPuzzle.Tree.LamGrid

/-! # The port algorithm in `O(n^(5/2) ln n)`

The `4`-ary hierarchy of depth `h` (`k = 4^h`, `q = 4h`) with the largest `h` such that
`(2²⁴ h² + 16λ) 16^h ≤ n`, and ports of side `σ = ⌊√X⌋ + 1` where `X` bounds the
reserve of a square. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The reserve bound that the ports must exceed. -/
def resX (n k q lam : ℕ) : ℕ :=
  2 * ((2 * (n / k) + 2 * k + (15 * lam + 1) * k) * (2 * k) + 4 * k * q) + 2

/-- The port side. -/
def portSide (n k q lam : ℕ) : ℕ := Nat.sqrt (resX n k q lam) + 1

theorem four_mul_le_pow : ∀ h : ℕ, 4 * h ≤ 4 ^ h
  | 0 => by simp
  | h + 1 => by
    have := four_mul_le_pow h
    have : 1 ≤ 4 ^ h := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]; omega

/-- The conditions of `optimalLength_le_port_lanes` for the `4`-ary hierarchy. -/
theorem optimalLength_le_hier4 {n h : ℕ} [NeZero n] (hh : 3 ≤ h)
    (hl : 64 ≤ GroupedOrder.lamN n)
    (hP : (2 ^ 24 * h ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ h ≤ n) (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * 4 ^ h) +
      2 * (520 * ((4 ^ h) ^ 2 * (n / 4 ^ h) ^ 3)) := by
  set lam := GroupedOrder.lamN n with hlam
  set k := 4 ^ h with hk
  have hk2 : k ^ 2 = 16 ^ h := by rw [hk, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hk64 : 64 ≤ k := by
    have : 4 ^ 3 ≤ 4 ^ h := Nat.pow_le_pow_right (by norm_num) hh
    rw [hk]; norm_num at this ⊢; omega
  have hkk : k * k = 16 ^ h := by rw [← hk2]; ring
  set q := h * 4 with hq
  have hqk : q ≤ k := by rw [hq, hk, mul_comm]; exact four_mul_le_pow h
  have h16 : 1 ≤ 16 ^ h := Nat.one_le_pow _ _ (by norm_num)
  -- the main inequality, in pieces
  have hP' := hP
  rw [add_mul] at hP'
  have hP1 : 2 ^ 24 * h ^ 2 * 16 ^ h ≤ n := by omega
  have hP2 : 16 * lam * 16 ^ h ≤ n := by omega
  have hh2 : 9 ≤ h ^ 2 := by nlinarith
  have hhh : h ≤ h ^ 2 := by nlinarith
  -- `c · 16^h ≤ n` for `c ≤ 2^24 h²`
  have hc : ∀ c, c ≤ 2 ^ 24 * h ^ 2 → c * 16 ^ h ≤ n := fun c hc =>
    le_trans (Nat.mul_le_mul_right _ hc) hP1
  have hkn : k * k ≤ n := by rw [hkk]; have := hc 1 (by omega); omega
  have hn1 : 1 ≤ n := by omega
  -- the port side
  set X := resX n k q lam with hX
  set σ := portSide n k q lam with hσdef
  set r := Nat.sqrt X with hr
  have hσr : σ = r + 1 := rfl
  have hrX : r * r ≤ X := Nat.sqrt_le X
  have hXσ : X < σ * σ := by rw [hσr]; exact Nat.lt_succ_sqrt X
  -- `X ≤ 13 n`
  have hsk : n / k * k ≤ n := Nat.div_mul_le_self n k
  have hX13 : X ≤ 13 * n := by
    have hlk : lam * (k * k) * 16 ≤ n := by
      rw [hkk]; have e : lam * 16 ^ h * 16 = 16 * lam * 16 ^ h := by ring
      omega
    have hq' : k * q ≤ k * k := Nat.mul_le_mul_left _ hqk
    have e : X = 8 * (n / k * k) + 8 * (k * k) + 60 * (lam * (k * k)) + 4 * (k * k) +
        8 * (k * q) + 2 := by
      rw [hX, resX]; ring
    have hkk' : 2 ^ 20 * (k * k) ≤ n := by rw [hkk]; exact hc _ (by omega)
    omega
  have h8 : 8 ≤ σ := by
    have hX64 : 64 ≤ X := by
      have e : X = 2 * ((2 * (n / k) + 2 * k + (15 * lam + 1) * k) * (2 * k) + 4 * k * q) + 2 := by
        rw [hX, resX]
      have a : 2 * k * (2 * k) ≤ (2 * (n / k) + 2 * k + (15 * lam + 1) * k) * (2 * k) :=
        Nat.mul_le_mul_right _ (by omega)
      have b : 64 ≤ 2 * k * (2 * k) := by
        have := Nat.mul_le_mul (show 2 ≤ 2 * k by omega) (show 32 ≤ 2 * k by omega)
        omega
      omega
    have : 8 ≤ r := by
      rw [hr]; exact Nat.le_sqrt'.2 (by omega)
    omega
  -- `60 h σ k ≤ n / 2`
  have hσk : 2 * (60 * h * σ * k) ≤ n := by
    have a1 : (240 * h * k) * (240 * h * k) * X ≤ n * n := by
      have e : (240 * h * k) * (240 * h * k) * X = 57600 * h ^ 2 * 16 ^ h * X := by
        rw [← hkk]; ring
      have b1 : 57600 * h ^ 2 * 16 ^ h * X ≤ 57600 * h ^ 2 * 16 ^ h * (13 * n) :=
        Nat.mul_le_mul_left _ hX13
      have b2 : 748800 * h ^ 2 * 16 ^ h ≤ n := hc _ (by omega)
      have b3 := Nat.mul_le_mul_right n b2
      have e2 : 57600 * h ^ 2 * 16 ^ h * (13 * n) = 748800 * h ^ 2 * 16 ^ h * n := by ring
      omega
    have a2 : 240 * h * k * r ≤ n := by
      have : (240 * h * k * r) * (240 * h * k * r) ≤ n * n := by
        have b := Nat.mul_le_mul_left ((240 * h * k) * (240 * h * k)) hrX
        have e : (240 * h * k * r) * (240 * h * k * r) = (240 * h * k) * (240 * h * k) * (r * r) := by
          ring
        omega
      exact Nat.mul_self_le_mul_self_iff.1 this
    have a3 : 240 * h * k ≤ n := by
      have b1 : 240 * h * 16 ^ h ≤ n := hc _ (by omega)
      have b2 : 240 * h * k ≤ 240 * h * (k * k) := Nat.mul_le_mul_left _ (Nat.le_mul_self k)
      rw [hkk] at b2
      omega
    have e : 2 * (60 * h * σ * k) = 120 * h * k * r + 120 * h * k := by rw [hσr]; ring
    have e2 : 240 * h * k * r = 2 * (120 * h * k * r) := by ring
    have e3 : 240 * h * k = 2 * (120 * h * k) := by ring
    omega
  have hhop : 2 * h * hopKc k q σ * k ≤ n := by
    unfold hopKc
    have e : 2 * h * (30 * σ + 20 * k * (q + 2) + 1200 * k + 3000) * k =
        60 * h * σ * k + (160 * h ^ 2 + 2480 * h) * 16 ^ h + 6000 * h * k := by
      rw [← hkk, hq]; ring
    have b1 : 2 * (2 * ((160 * h ^ 2 + 2480 * h) * 16 ^ h)) ≤ n := by
      have := hc (4 * (160 * h ^ 2 + 2480 * h)) (by omega)
      have e : 2 * (2 * ((160 * h ^ 2 + 2480 * h) * 16 ^ h)) = 4 * (160 * h ^ 2 + 2480 * h) * 16 ^ h := by
        ring
      omega
    have b2 : 4 * (6000 * h * k) ≤ n := by
      have := hc (24000 * h) (by omega)
      have b : 6000 * h * k ≤ 6000 * h * (k * k) := Nat.mul_le_mul_left _ (Nat.le_mul_self k)
      rw [hkk] at b
      have e : 24000 * h * 16 ^ h = 4 * (6000 * h * 16 ^ h) := by ring
      omega
    omega
  have hph : 8 * (2 * h + 1) * k * q * k ≤ n := by
    have e : 8 * (2 * h + 1) * k * q * k = (64 * h ^ 2 + 32 * h) * 16 ^ h := by rw [← hkk, hq]; ring
    rw [e]; exact hc _ (by omega)
  have hlo : 8 * k * q * k ≤ n := by
    have e : 8 * k * q * k = (32 * h) * 16 ^ h := by rw [← hkk, hq]; ring
    rw [e]; exact hc _ (by omega)
  have hlo2 : 16 * k * lam * k ≤ n := by
    have e : 16 * k * lam * k = 16 * lam * (k * k) := by ring
    rw [e, hkk]; exact hP2
  have hσX : resX n k q lam ≤ σ ^ 2 := by rw [sq]; omega
  have hsys := Hier.tight (b := 4) (h := h) (by norm_num) (by omega)
  have hke : Even k := by
    rw [hk]; exact (Nat.even_pow.2 ⟨by decide, by omega⟩)
  have hqe : Even q := ⟨h * 2, by rw [hq]; ring⟩
  have := optimalLength_le_port_lanes (h := h) (Hier.sys 4 h (by norm_num) (by omega)) hsys rfl
    (by omega) hke hqe (by omega) hqk hk64 hl hlo hlo2 hph hhop h8 hσX B
  exact this

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The depth: the largest `h` with `(2²⁴ h² + 16λ) 16^h ≤ n`. -/
def portDepth (n : ℕ) : ℕ :=
  Nat.findGreatest (fun h => (2 ^ 24 * h ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ h ≤ n) n

theorem portDepth_spec {n : ℕ} (hn : 2 ^ 41 ≤ n) :
    3 ≤ portDepth n ∧
      (2 ^ 24 * portDepth n ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ portDepth n ≤ n ∧
      n < (2 ^ 24 * (portDepth n + 1) ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ (portDepth n + 1) := by
  have hl := lam_small (le_trans (by norm_num) hn)
  have hP3 : (2 ^ 24 * 3 ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ 3 ≤ n := by
    norm_num at hn ⊢; omega
  have h3 : 3 ≤ portDepth n := Nat.le_findGreatest (by omega) hP3
  have hP : (2 ^ 24 * portDepth n ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ portDepth n ≤ n :=
    Nat.findGreatest_spec (P := fun h => (2 ^ 24 * h ^ 2 + 16 * GroupedOrder.lamN n) * 16 ^ h ≤ n)
      (m := 3) (by omega) hP3
  refine ⟨h3, hP, ?_⟩
  by_contra hc
  push Not at hc
  have hlt : portDepth n < portDepth n + 1 := by omega
  have hle : portDepth n + 1 ≤ n := by
    have a : portDepth n < 16 ^ portDepth n := Nat.lt_pow_self (by norm_num)
    have b : 16 ^ portDepth n ≤ n := by
      have : 1 ≤ 2 ^ 24 * portDepth n ^ 2 + 16 * GroupedOrder.lamN n := by
        have : 1 ≤ portDepth n ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      nlinarith
    omega
  exact Nat.findGreatest_is_greatest hlt hle hc

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

theorem log_coef {n h : ℕ} (hn : 2 ^ 41 ≤ n) (h16 : 16 ^ h ≤ n) (hpl : 2 ^ Nat.log 2 n ≤ n) :
    4160 * (4096 * ((h : ℝ) + 1) + 12 * ((Nat.log 2 n : ℝ) + 1)) + 32 ≤ 2 ^ 24 * Real.log n := by
  have hlog2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL41 : 41 * Real.log 2 ≤ Real.log n := by
    have c : ((2 ^ 41 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    rw [Nat.cast_pow, Nat.cast_ofNat] at c
    have := Real.log_le_log (by positivity) c
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hLh : (h : ℝ) * (4 * Real.log 2) ≤ Real.log n := by
    have c : ((16 ^ h : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 h16
    push_cast at c
    have := Real.log_le_log (by positivity) c
    rw [Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have hLl : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have c : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hpl
    push_cast at c
    have := Real.log_le_log (by positivity) c
    rw [Real.log_pow] at this; linarith
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have a1 : (h : ℝ) * 2.7724 ≤ Real.log n := by
    have := mul_le_mul_of_nonneg_left (show (2.7724 : ℝ) ≤ 4 * Real.log 2 by linarith) hh0
    linarith
  have a2 : (Nat.log 2 n : ℝ) * 0.6931 ≤ Real.log n := by
    have := mul_le_mul_of_nonneg_left (show (0.6931 : ℝ) ≤ Real.log 2 by linarith) hl0
    linarith
  have a3 : (28.41 : ℝ) ≤ Real.log n := by linarith
  linarith

/-- **The port algorithm is within `2²⁴ n^(5/2) ln n` of the Manhattan bound.** -/
theorem port_optimalLength_le {n : ℕ} [NeZero n] (hn : 2 ^ 41 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 ^ 24 * (n : ℝ) ^ ((5 : ℝ) / 2) * Real.log n := by
  have hpl : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h3003 : 3003 ≤ n := by omega
  have hn3003' : ((3003 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 h3003
  obtain ⟨h3, hP, hnot⟩ := portDepth_spec hn
  have F4' : 16 ^ portDepth n ≤ n := by
    have : 1 ≤ 2 ^ 24 * portDepth n ^ 2 + 16 * GroupedOrder.lamN n := by
      have : 1 ≤ portDepth n ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    nlinarith
  have hcoef0 := log_coef hn F4' hpl
  set h := portDepth n with hhdef
  set lam := GroupedOrder.lamN n with hlam
  have hl : 64 ≤ lam := by have := lam_ge (le_trans (by norm_num) hn); omega
  have hnat := optimalLength_le_hier4 h3 hl hP B
  set k := 4 ^ h with hk
  have hk2 : k * k = 16 ^ h := by rw [hk, ← pow_add, ← two_mul, pow_mul]; norm_num
  have hk0 : 0 < k := by positivity
  -- natural facts
  have F1 : n / k * k ≤ n := Nat.div_mul_le_self n k
  have F4 : 16 ^ h ≤ n := by
    have : 1 ≤ 2 ^ 24 * h ^ 2 + 16 * lam := by
      have : 1 ≤ h ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    nlinarith
  have F2 : k * k ≤ n := by rw [hk2]; exact F4
  set A := 4096 * (h + 1) + 4 * lam with hA
  have F3 : n ≤ 16 * (A * A) * (k * k) := by
    have e : (2 ^ 24 * (h + 1) ^ 2 + 16 * lam) * 16 ^ (h + 1) =
        16 * (2 ^ 24 * (h + 1) ^ 2 + 16 * lam) * 16 ^ h := by ring
    have hM : 2 ^ 24 * (h + 1) ^ 2 + 16 * lam ≤ A * A := by
      rw [hA]
      have : 16 * lam ≤ 16 * lam * lam := by nlinarith
      nlinarith
    rw [hk2]
    have := Nat.mul_le_mul_right (16 ^ h) (Nat.mul_le_mul_left 16 hM)
    omega
  -- reals
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set nr : ℝ := (n : ℝ) with hnr
  set K : ℝ := (k : ℝ) with hK
  have hK0 : 0 < K := by rw [hK]; exact_mod_cast hk0
  set Ar : ℝ := (A : ℝ) with hAr
  have hA0 : 0 ≤ Ar := by positivity
  set P : ℝ := nr ^ ((5 : ℝ) / 2) with hP
  have hsn : 0 ≤ Real.sqrt nr := Real.sqrt_nonneg _
  have hPe : P = nr ^ 2 * Real.sqrt nr := by
    rw [hP, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have hsq_n : Real.sqrt nr ^ 2 = nr := Real.sq_sqrt hn0.le
  -- `√n ≤ 4 A K` and `K ≤ √n`
  have hup : Real.sqrt nr ≤ 4 * Ar * K := by
    have h1 : nr ≤ (4 * Ar * K) ^ 2 := by
      have : (n : ℝ) ≤ 16 * ((A : ℝ) * A) * ((k : ℝ) * k) := by exact_mod_cast F3
      rw [hnr, hAr, hK]; nlinarith
    calc Real.sqrt nr ≤ Real.sqrt ((4 * Ar * K) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 4 * Ar * K := Real.sqrt_sq (by positivity)
  have hdown : K ≤ Real.sqrt nr := by
    have h1 : K ^ 2 ≤ nr := by
      have : ((k : ℝ) * k) ≤ n := by exact_mod_cast F2
      rw [hK, hnr]; nlinarith
    calc K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK0.le).symm
      _ ≤ Real.sqrt nr := Real.sqrt_le_sqrt h1
  -- the main term
  set m : ℝ := ((n / k : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hmK : m * K ≤ nr := by
    have : ((n / k : ℕ) : ℝ) * (k : ℝ) ≤ n := by exact_mod_cast F1
    rw [hm, hK, hnr]; exact this
  have hmain : K ^ 2 * m ^ 3 ≤ 4 * Ar * P := by
    have h1 : K ^ 2 * m ^ 3 * K ≤ nr ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hmK 3
      calc K ^ 2 * m ^ 3 * K = (m * K) ^ 3 := by ring
        _ ≤ _ := this
    have h2 : nr ^ 3 ≤ 4 * Ar * P * K := by
      rw [hPe]
      have e3 : nr ^ 3 = nr ^ 2 * Real.sqrt nr * Real.sqrt nr := by
        rw [mul_assoc, ← sq, hsq_n]; ring
      rw [e3]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ nr ^ 2 * Real.sqrt nr)
      calc nr ^ 2 * Real.sqrt nr * Real.sqrt nr ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_right (le_trans h1 h2) hK0
  have hfirst : 2 * ((15 * nr ^ 2 + 3002 * nr + 1) * K) ≤ 32 * P := by
    have hn3003 : (3003 : ℝ) ≤ nr := by
      have c := hn3003'
      push_cast at c
      exact c
    have ha : 15 * nr ^ 2 + 3002 * nr + 1 ≤ 16 * nr ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right ha hK0.le
    have h2 := mul_le_mul_of_nonneg_left hdown (by positivity : (0 : ℝ) ≤ nr ^ 2)
    rw [hPe]; linarith
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * nr ^ 2 + 3002 * nr + 1) * K) + 2 * (520 * (K ^ 2 * m ^ 3)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    rw [hnr, hK, hm]
    exact this
  -- logarithms
  have hAe : Ar = 4096 * ((h : ℝ) + 1) + 12 * ((Nat.log 2 n : ℝ) + 1) := by
    rw [hAr, hA, hlam]; unfold GroupedOrder.lamN; push_cast; ring
  have hcoef : 4160 * Ar + 32 ≤ 2 ^ 24 * Real.log nr := by
    rw [hAe]; linarith
  have hP0 : 0 ≤ P := by rw [hPe]; positivity
  calc (optimalLength B : ℝ) ≤ _ := hcast
    _ ≤ (manhattan B.val : ℝ) + 32 * P + 4160 * Ar * P := by linarith
    _ = (manhattan B.val : ℝ) + (4160 * Ar + 32) * P := by ring
    _ ≤ (manhattan B.val : ℝ) + 2 ^ 24 * Real.log nr * P := by
        have := mul_le_mul_of_nonneg_right hcoef hP0
        linarith
    _ = _ := by rw [hP, hnr]; ring

end SlidingPuzzle.Port
