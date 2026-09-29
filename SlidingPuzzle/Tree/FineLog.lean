import SlidingPuzzle.Tree.FineAccounting

/-! # Accounting against the logarithmic slack

`FineAccounting` bounds the certified cost once `2048·depth·k ≤ s`. Here the only
hypotheses are the ones the run needs anyway, `8kq ≤ s` and `16kλ ≤ s`, together with
`λ ≥ 64` and `k ≥ 64`: then `treeBound ≤ (48·depth + 142) k² s³`. The depth enters only
through the hops (`≈ 46.3`) and the stock (`≈ 1.5`); the constant collects the preload
(`≈ 51.3`), the relocations (`≈ 57.2`), the cleanup and Finish (`≈ 32`). -/
namespace SlidingPuzzle.Tree
open Finset

namespace FineLog

/-- Monomial bounds against `k² s³` from `64 ≤ k`, `8kq ≤ s` and `1024k ≤ s`. -/
theorem monomials {k q s lam : ℕ} (hk : 64 ≤ k) (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s)
    (hks : 1024 * k ≤ s) :
    8 * (k ^ 3 * q * s ^ 2) ≤ k ^ 2 * s ^ 3 ∧
    128 * (lam * k ^ 4 * q * s) ≤ k ^ 2 * s ^ 3 ∧
    8192 * (k ^ 4 * q * s) ≤ k ^ 2 * s ^ 3 ∧
    1024 * (k ^ 3 * s ^ 2) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k ^ 2 * s ^ 2) ≤ k ^ 2 * s ^ 3 ∧
    64 * (k * s ^ 3) ≤ k ^ 2 * s ^ 3 ∧
    512 * (k ^ 2 * q * s ^ 2) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k ^ 3 * q * s) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k ^ 3 * s) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k ^ 2 * q * s) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k ^ 2 * s) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k * s ^ 2) ≤ k ^ 2 * s ^ 3 ∧
    65536 * (k * s) ≤ k ^ 2 * s ^ 3 ∧
    65536 * s ^ 3 ≤ 16 * (k ^ 2 * s ^ 3) ∧
    65536 * s ^ 2 ≤ k ^ 2 * s ^ 3 ∧
    65536 * s ≤ k ^ 2 * s ^ 3 ∧
    65536 * k ^ 3 ≤ k ^ 2 * s ^ 3 ∧
    65536 * k ^ 2 ≤ k ^ 2 * s ^ 3 ∧
    65536 ≤ k ^ 2 * s ^ 3 := by
  have hs : 65536 ≤ s := by omega
  have hk1 : 1 ≤ k := by omega
  have hs1 : 1 ≤ s := by omega
  have hks2 : k ≤ s := by omega
  have hX : k ^ 2 * s ^ 2 * 65536 ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hs
    calc k ^ 2 * s ^ 2 * 65536 ≤ k ^ 2 * s ^ 2 * s := this
      _ = _ := by ring
  have m1 : 8 * (k ^ 3 * q * s ^ 2) ≤ k ^ 2 * s ^ 3 := Fine.f1 hkq
  have m2 : 128 * (lam * k ^ 4 * q * s) ≤ k ^ 2 * s ^ 3 := Fine.f2 hkq hkl
  have m3 : 8192 * (k ^ 4 * q * s) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s) (Nat.mul_le_mul hks hkq)
    calc 8192 * (k ^ 4 * q * s) = 1024 * k * (8 * k * q) * (k ^ 2 * s) := by ring
      _ ≤ s * s * (k ^ 2 * s) := this
      _ = _ := by ring
  have m4 : 1024 * (k ^ 3 * s ^ 2) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s ^ 2) hks
    calc 1024 * (k ^ 3 * s ^ 2) = 1024 * k * (k ^ 2 * s ^ 2) := by ring
      _ ≤ s * (k ^ 2 * s ^ 2) := this
      _ = _ := by ring
  have m5 : 65536 * (k ^ 2 * s ^ 2) ≤ k ^ 2 * s ^ 3 := by linarith
  have m6 : 64 * (k * s ^ 3) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k * s ^ 3) hk
    calc 64 * (k * s ^ 3) ≤ k * (k * s ^ 3) := this
      _ = _ := by ring
  have m7 : 512 * (k ^ 2 * q * s ^ 2) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (8 * (k ^ 2 * q * s ^ 2)) hk
    have e : k * (8 * (k ^ 2 * q * s ^ 2)) = 8 * (k ^ 3 * q * s ^ 2) := by ring
    linarith
  -- small monomials: each is at most `k² s² ≤ k² s³ / 65536`
  have hkq' : k * q ≤ s := by
    have e : 8 * k * q = 8 * (k * q) := by ring
    omega
  have hq : q ≤ s := le_trans (Nat.le_mul_of_pos_left q (by omega)) hkq'
  have hkss : k * s ≤ k ^ 2 * s ^ 2 := Fine.f8 hk1 hs1
  have t1 : k ^ 3 * q * s ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s) hkq'
    calc k ^ 3 * q * s = k * q * (k ^ 2 * s) := by ring
      _ ≤ s * (k ^ 2 * s) := this
      _ = _ := by ring
  have t2 : k ^ 3 * s ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s) hks2
    calc k ^ 3 * s = k * (k ^ 2 * s) := by ring
      _ ≤ s * (k ^ 2 * s) := this
      _ = _ := by ring
  have t3 : k ^ 2 * q * s ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s) hq
    calc k ^ 2 * q * s = q * (k ^ 2 * s) := by ring
      _ ≤ s * (k ^ 2 * s) := this
      _ = _ := by ring
  have t4 : k ^ 2 * s ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s) hs1
    calc k ^ 2 * s = k ^ 2 * s * 1 := by ring
      _ ≤ k ^ 2 * s * s := this
      _ = _ := by ring
  have t5 : k * s ^ 2 ≤ k ^ 2 * s ^ 2 := by
    have := Nat.mul_le_mul_right (k * s ^ 2) hk1
    calc k * s ^ 2 = 1 * (k * s ^ 2) := by ring
      _ ≤ k * (k * s ^ 2) := this
      _ = _ := by ring
  have t6 : 65536 * s ^ 3 ≤ 16 * (k ^ 2 * s ^ 3) := by
    have hk2 : 4096 ≤ k ^ 2 := by
      have := Nat.mul_le_mul hk hk
      calc 4096 = 64 * 64 := by norm_num
        _ ≤ k * k := this
        _ = k ^ 2 := by ring
    have := Nat.mul_le_mul_right (s ^ 3) hk2
    have e : 16 * (k ^ 2 * s ^ 3) = 16 * (k ^ 2 * s ^ 3) := rfl
    linarith
  have t7 : s ^ 2 ≤ k ^ 2 * s ^ 2 := by
    have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul_right (s ^ 2) hk2
    linarith
  have t8 : s ≤ s ^ 2 := by
    have := Nat.mul_le_mul_left s hs1
    calc s = s * 1 := by ring
      _ ≤ s * s := this
      _ = s ^ 2 := by ring
  have t9 : k ^ 3 ≤ k ^ 2 * s ^ 2 := by
    have : k ^ 3 ≤ k ^ 3 * s := Nat.le_mul_of_pos_right _ (by omega)
    linarith [t2]
  have t10 : k ^ 2 ≤ k ^ 2 * s := Nat.le_mul_of_pos_right _ (by omega)
  have t11 : 1 ≤ k ^ 2 * s ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨m1, m2, m3, m4, m5, m6, m7, ?_, ?_, ?_, ?_, ?_, ?_, t6, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith

end FineLog

open FineLog in
/-- Pure polynomial estimate with the reserve inputs kept exact. -/
theorem polynomial_budget_log (k q s d lam lc nd rv : ℕ)
    (hk : 64 ≤ k) (hlam : 64 ≤ lam) (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s)
    (hlc : lc ≤ 2 * k ^ 2 * q * s)
    (hnd : nd ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q)
    (hrv : rv ≤ 6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :
    2 * (k * s) + 52 * (k * s) * rv +
      runCost (k * s) k q s d lc nd +
      (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) +
          9354 * k ^ 2 * (k * s))) / 2 ≤
      (48 * d + 142) * (k ^ 2 * s ^ 3) := by
  have hks : 1024 * k ≤ s := by
    have : 1024 * k ≤ 16 * k * lam := by
      have := Nat.mul_le_mul_left (16 * k) hlam
      calc 1024 * k = 16 * k * 64 := by ring
        _ ≤ _ := this
    omega
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18,
    m19⟩ := monomials hk hkq hkl hks
  -- the reserve inputs, multiplied out
  have Pnd : (k * s) * nd ≤ (k * s) * (4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q) :=
    Nat.mul_le_mul_left _ hnd
  have Prv : (k * s) * rv ≤
      (k * s) * (6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :=
    Nat.mul_le_mul_left _ hrv
  have Plc : (k * s) * lc ≤ (k * s) * (2 * k ^ 2 * q * s) := Nat.mul_le_mul_left _ hlc
  have Pdnd : d * ((k * s) * nd) ≤
      d * ((k * s) * (4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q)) :=
    Nat.mul_le_mul_left _ Pnd
  have Plc2 : 3 * (s + 3) * (14 * k + 18) * lc ≤
      3 * (s + 3) * (14 * k + 18) * (2 * k ^ 2 * q * s) :=
    Nat.mul_le_mul_left _ hlc
  -- depth-weighted monomials
  have d1 := Nat.mul_le_mul_left d m1
  have d2 := Nat.mul_le_mul_left d m2
  have d3 := Nat.mul_le_mul_left d m3
  have d4 := Nat.mul_le_mul_left d m4
  have d5 := Nat.mul_le_mul_left d m5
  have Pdiv : (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
      (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s))) / 2 ≤
      32 * (k ^ 2 * s ^ 3) := by
    apply Nat.div_le_of_le_mul
    linarith
  have hdX : 0 ≤ d * (k ^ 2 * s ^ 3) := Nat.zero_le _
  unfold runCost hopK
  linarith

end SlidingPuzzle.Tree
