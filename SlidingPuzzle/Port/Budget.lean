import SlidingPuzzle.Port.Transport
import SlidingPuzzle.Tree.FineLog

/-! # The port bound is a constant times `k² s³`

Besides the tree constraints `8kq ≤ s` and `16kλ ≤ s`, and `14(q+2)k ≤ s` for the lane
crossings (charged by distance, `2k` per tile), the depth enters only through
`2d·hopKc ≤ s` (the cheap hops of a tile) and `128(2d+1)q ≤ s` (imports at placeholders;
the placeholders' junk is charged by the distance of their hops, `s·(2k+2d)` per unit of need). -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Tree

section budget

variable {k q s d lam σ lc nd rv : ℕ}

/-- The needs, against `Y = k² q s`. -/
theorem needs_le (hk : 64 ≤ k) (hkl : 16 * k * lam ≤ s) (hks : 1024 * k ≤ s) (hq : 1 ≤ q)
    (hs : 65536 ≤ s)
    (hnd : nd ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q)
    (hrv : rv ≤ 6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :
    nd ≤ 6 * (k ^ 2 * q * s) ∧ rv ≤ 9 * (k ^ 2 * q * s) := by
  have hlk : (14 + 30 * lam) * k ≤ 2 * s := by
    have e : (14 + 30 * lam) * k = 14 * k + 30 * (k * lam) := by ring
    have e2 : 16 * k * lam = 16 * (k * lam) := by ring
    omega
  have h1 : (14 + 30 * lam) * k ^ 3 * q ≤ 2 * (k ^ 2 * q * s) := by
    have := Nat.mul_le_mul_right (k ^ 2 * q) hlk
    calc (14 + 30 * lam) * k ^ 3 * q = (14 + 30 * lam) * k * (k ^ 2 * q) := by ring
      _ ≤ 2 * s * (k ^ 2 * q) := this
      _ = _ := by ring
  have h2 : 6 * k ^ 2 ≤ k ^ 2 * q * s := by
    have : 6 ≤ q * s := by nlinarith
    calc 6 * k ^ 2 ≤ q * s * k ^ 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  have e1 : 4 * k ^ 2 * q * s = 4 * (k ^ 2 * q * s) := by ring
  have e2 : 6 * k ^ 2 * q * s = 6 * (k ^ 2 * q * s) := by ring
  constructor <;> omega

/-- The placeholder product `(2d+1) nd`, which pays for the imports of placeholders. -/
theorem ph_le (hph : 128 * (2 * d + 1) * q ≤ s) (hnd6 : nd ≤ 6 * (k ^ 2 * q * s)) :
    16 * (s * ((2 * d + 1) * nd)) ≤ k ^ 2 * s ^ 3 := by
  have h1 : (2 * d + 1) * nd ≤ (2 * d + 1) * (6 * (k ^ 2 * q * s)) := Nat.mul_le_mul_left _ hnd6
  have h3 := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hph
  have h4 : 16 * (s * ((2 * d + 1) * nd)) ≤ 16 * (s * ((2 * d + 1) * (6 * (k ^ 2 * q * s)))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
  have e : 16 * (s * ((2 * d + 1) * (6 * (k ^ 2 * q * s)))) * 4 =
      3 * (k ^ 2 * s ^ 2 * (128 * (2 * d + 1) * q)) := by ring
  have e2 : k ^ 2 * s ^ 2 * s = k ^ 2 * s ^ 3 := by ring
  omega

/-- The relocation weight. -/
theorem relocW_le (hk : 64 ≤ k) (hkq : 8 * k * q ≤ s) (hks : 1024 * k ≤ s) (hs : 65536 ≤ s)
    (hlc : lc ≤ 2 * k ^ 2 * q * s) : relocW k s lc ≤ 21 * (k ^ 2 * s ^ 2) := by
  unfold relocW
  have e1 : s ^ 2 * (15 * k ^ 2 + 30 * k + 18) ≤ 16 * (k ^ 2 * s ^ 2) := by
    have a : 30 * k + 18 ≤ k ^ 2 := by
      have := Nat.mul_le_mul_right k hk
      have e : k ^ 2 = k * k := by ring
      omega
    calc s ^ 2 * (15 * k ^ 2 + 30 * k + 18) ≤ s ^ 2 * (16 * k ^ 2) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have f1 : (14 * k + 18) * lc ≤ 30 * k ^ 3 * q * s := by
    have := Nat.mul_le_mul (show 14 * k + 18 ≤ 15 * k by omega) hlc
    calc (14 * k + 18) * lc ≤ 15 * k * (2 * k ^ 2 * q * s) := this
      _ = _ := by ring
  have f2 : 30 * k ^ 3 * q * s ≤ 4 * (k ^ 2 * s ^ 2) := by
    have := Nat.mul_le_mul_left (4 * (k ^ 2 * s)) hkq
    have e1 : 4 * (k ^ 2 * s) * (8 * k * q) = 32 * (k ^ 3 * q * s) := by ring
    have e2 : 30 * k ^ 3 * q * s = 30 * (k ^ 3 * q * s) := by ring
    have e3 : 4 * (k ^ 2 * s) * s = 4 * (k ^ 2 * s ^ 2) := by ring
    omega
  have f3 : (14 * k + 18) * k ^ 2 ≤ k ^ 2 * s ^ 2 := by
    have a : 14 * k + 18 ≤ s ^ 2 := by
      have := Nat.le_mul_self s
      have e : s ^ 2 = s * s := by ring
      omega
    calc (14 * k + 18) * k ^ 2 ≤ s ^ 2 * k ^ 2 := Nat.mul_le_mul_right _ a
      _ = _ := by ring
  have e2 : (14 * k + 18) * (lc + k ^ 2) = (14 * k + 18) * lc + (14 * k + 18) * k ^ 2 := by ring
  omega

end budget

theorem port_budget (k q s d lam σ lc nd rv : ℕ)
    (hk : 64 ≤ k) (hlam : 64 ≤ lam) (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s)
    (hq : 1 ≤ q) (hd : 1 ≤ d) (hhop : 2 * d * hopKc k σ ≤ s) (hcr : 14 * (q + 2) * k ≤ s)
    (hph : 128 * (2 * d + 1) * q ≤ s)
    (hlc : lc ≤ 2 * k ^ 2 * q * s)
    (hnd : nd ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q)
    (hrv : rv ≤ 6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :
    2 * (k * s) + 2 * s + 52 * (k * s) * rv +
      prunCost (k * s) k q s σ d lc nd (relocW k s lc) +
      (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) +
          9354 * k ^ 2 * (k * s))) / 2 ≤
      520 * (k ^ 2 * s ^ 3) := by
  have hks : 1024 * k ≤ s := by
    have : 1024 * k ≤ 16 * k * lam := by
      have := Nat.mul_le_mul_left (16 * k) hlam
      calc 1024 * k = 16 * k * 64 := by ring
        _ ≤ _ := this
    omega
  have hs : 65536 ≤ s := by omega
  obtain ⟨hnd6, hrv9⟩ := needs_le hk hkl hks hq hs hnd hrv
  have hZ := ph_le (k := k) (d := d) hph hnd6
  have hW := relocW_le hk hkq hks hs hlc
  -- monomials against `U = k² s³`
  have hY8 : 8 * (k * s * (k ^ 2 * q * s)) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hkq
    calc 8 * (k * s * (k ^ 2 * q * s)) = k ^ 2 * s ^ 2 * (8 * k * q) := by ring
      _ ≤ k ^ 2 * s ^ 2 * s := this
      _ = _ := by ring
  have hks3 : 64 * (k * s ^ 3) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k * s ^ 3) hk
    calc 64 * (k * s ^ 3) ≤ k * (k * s ^ 3) := this
      _ = _ := by ring
  have g5 : 65536 * (k ^ 2 * s ^ 2) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hs
    calc 65536 * (k ^ 2 * s ^ 2) = k ^ 2 * s ^ 2 * 65536 := by ring
      _ ≤ k ^ 2 * s ^ 2 * s := this
      _ = _ := by ring
  have g6 : k * s ≤ k ^ 2 * s ^ 2 := by
    have := Nat.le_mul_self (k * s)
    have e : k ^ 2 * s ^ 2 = k * s * (k * s) := by ring
    omega
  have g7 : s ≤ k * s := Nat.le_mul_of_pos_left _ (by omega)
  -- the per-event budgets
  have hσ : 30 * σ ≤ s := by
    have h1 : 30 * σ ≤ hopKc k σ := by unfold hopKc; omega
    have h2 : hopKc k σ ≤ 2 * d * hopKc k σ :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hKi : hopKi k s σ ≤ 13 * s := by unfold hopKi; omega
  have hKx : xferK k s σ ≤ 33 * s := by unfold xferK; omega
  have hA : legA k s σ ≤ 4 * s := by unfold legA; omega
  -- the terms
  have t1 : hopKc k σ * (2 * d * (k * s) ^ 2) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s ^ 2) hhop
    calc hopKc k σ * (2 * d * (k * s) ^ 2) = 2 * d * hopKc k σ * (k ^ 2 * s ^ 2) := by ring
      _ ≤ s * (k ^ 2 * s ^ 2) := this
      _ = _ := by ring
  have t2 : hopKi k s σ * (2 * (k * s) ^ 2 + (2 * d + 1) * nd) ≤ 27 * (k ^ 2 * s ^ 3) := by
    have h1 := Nat.mul_le_mul_right (2 * (k * s) ^ 2 + (2 * d + 1) * nd) hKi
    have e : 13 * s * (2 * (k * s) ^ 2 + (2 * d + 1) * nd) =
        26 * (k ^ 2 * s ^ 3) + 13 * (s * ((2 * d + 1) * nd)) := by ring
    omega
  have t3 : xferK k s σ * (4 * (k * s) ^ 2) ≤ 132 * (k ^ 2 * s ^ 3) := by
    have := Nat.mul_le_mul_right (4 * (k * s) ^ 2) hKx
    have e : 33 * s * (4 * (k * s) ^ 2) = 132 * (k ^ 2 * s ^ 3) := by ring
    omega
  have t4 : s * ((2 * k + 2 * d) * nd) ≤ 2 * (k ^ 2 * s ^ 3) := by
    have a1 : k * s * nd ≤ k * s * (6 * (k ^ 2 * q * s)) := Nat.mul_le_mul_left _ hnd6
    have a2 : 2 * d * nd ≤ (2 * d + 1) * nd := Nat.mul_le_mul_right _ (by omega)
    have a3 := Nat.mul_le_mul_left s a2
    have e : s * ((2 * k + 2 * d) * nd) = 2 * (k * s * nd) + s * (2 * d * nd) := by ring
    have e2 : k * s * (6 * (k ^ 2 * q * s)) = 6 * (k * s * (k ^ 2 * q * s)) := by ring
    omega
  have t5 : 3 * legA k s σ * relocW k s lc ≤ 252 * (k ^ 2 * s ^ 3) := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hA) hW
    have e : 3 * (4 * s) * (21 * (k ^ 2 * s ^ 2)) = 252 * (k ^ 2 * s ^ 3) := by ring
    omega
  have t6 : lc * (k * s) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k * s) hlc
    have e : 2 * k ^ 2 * q * s * (k * s) = 2 * (k * s * (k ^ 2 * q * s)) := by ring
    omega
  have t7 : 52 * (k * s) * rv ≤ 59 * (k ^ 2 * s ^ 3) := by
    have := Nat.mul_le_mul_left (52 * (k * s)) hrv9
    have e : 52 * (k * s) * (9 * (k ^ 2 * q * s)) = 468 * (k * s * (k ^ 2 * q * s)) := by ring
    omega
  have t8 : (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
      (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s))) / 2 ≤
      40 * (k ^ 2 * s ^ 3) := by
    apply Nat.div_le_of_le_mul
    have hlc' : lc ≤ 2 * (k ^ 2 * q * s) := by
      have e : 2 * k ^ 2 * q * s = 2 * (k ^ 2 * q * s) := by ring
      omega
    have g1 : lc + (nd + (rv + lc)) ≤ 19 * (k ^ 2 * q * s) := by omega
    have g2 : 26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) ≤
        26 * (k * s) * (19 * (k ^ 2 * q * s) + 2 * (k * s) + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : 26 * (k * s) * (19 * (k ^ 2 * q * s) + 2 * (k * s) + 5) =
        494 * (k * s * (k ^ 2 * q * s)) + 52 * (k ^ 2 * s ^ 2) + 130 * (k * s) := by ring
    have g3 : k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) ≤ 6 * (k ^ 2 * s ^ 3) := by
      have a : 1509 * s ^ 2 + 1505 * s + 4796 ≤ s ^ 3 := by
        have h1 := Nat.mul_le_mul_right (s ^ 2) hs
        have e : s ^ 3 = s * s ^ 2 := by ring
        have h2 : s ≤ s ^ 2 := by
          have := Nat.le_mul_self s
          have e : s ^ 2 = s * s := by ring
          omega
        omega
      calc k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) ≤ k ^ 2 * (6 * s ^ 3) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    have g4 : 9354 * k ^ 2 * (k * s) ≤ k ^ 2 * s ^ 3 := by
      have a : 9354 * k ≤ s ^ 2 := by
        have := Nat.mul_le_mul hks hs
        have e : s ^ 2 = s * s := by ring
        omega
      calc 9354 * k ^ 2 * (k * s) = k ^ 2 * s * (9354 * k) := by ring
        _ ≤ k ^ 2 * s * s ^ 2 := Nat.mul_le_mul_left _ a
        _ = _ := by ring
    omega
  have hsmall : 2 * (k * s) + 2 * s ≤ k ^ 2 * s ^ 3 := by omega
  have t9 : 7 * (q + 2) * (2 * k * (k * s) ^ 2) ≤ k ^ 2 * s ^ 3 := by
    have := Nat.mul_le_mul_right (k ^ 2 * s ^ 2) hcr
    calc 7 * (q + 2) * (2 * k * (k * s) ^ 2) = 14 * (q + 2) * k * (k ^ 2 * s ^ 2) := by ring
      _ ≤ s * (k ^ 2 * s ^ 2) := this
      _ = _ := by ring
  unfold prunCost
  omega

end SlidingPuzzle.Port
