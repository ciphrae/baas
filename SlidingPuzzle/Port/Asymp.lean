import SlidingPuzzle.Port.Lanes

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
