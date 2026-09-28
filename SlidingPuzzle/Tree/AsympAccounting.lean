import SlidingPuzzle.Tree.Transport
import SlidingPuzzle.Tree.Hier

/-! # Coarse polynomial accounting for the tree algorithm

These estimates deliberately sacrifice constants. The aim is an unconditional
exponent below 8/3, keeping all feasibility conditions explicit.
-/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {n k s q : ℕ} (L : LaneSys k q)

theorem sum_laneI (f : LaneI k q → ℕ) :
    ∑ H, f H = ∑ b : Fin k, ∑ o : Fin q, ∑ t : Fin k, ∑ side : Bool,
      f ⟨b, o, t, side⟩ := by
  let e : LaneI k q ≃ Fin k × Fin q × Fin k × Bool :=
    ⟨fun H => (H.b, H.o, H.t, H.side), fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  simpa only [Fintype.sum_prod_type, e, Equiv.coe_fn_mk] using
    (Equiv.sum_comp e (fun p => f ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩))

theorem sum_blen_le : ∑ H : LaneI k q, blen L H ≤ k ^ 2 * q := by
  rw [sum_laneI]
  calc
    _ ≤ ∑ _b : Fin k, ∑ _o : Fin q, k := by
      apply sum_le_sum; intro b _
      apply sum_le_sum; intro o _
      exact L.sum_len_offset o
    _ = _ := by simp; ring

theorem laneCells_bound : laneCells L s ≤ 2 * k ^ 2 * q * s := by
  unfold laneCells rowLen colLen
  rw [← sum_mul, ← sum_mul]
  have h1 := Nat.mul_le_mul_right s (sum_blen_le L)
  have h2 := Nat.mul_le_mul (sum_blen_le L) (Nat.sub_le s q)
  nlinarith

theorem sum_blen_axes_le : ∑ l : Ln k q, blen L l.2 ≤ 2 * k ^ 2 * q := by
  simp only [Ln, Fintype.sum_prod_type, Fintype.sum_bool]
  have := sum_blen_le L
  nlinarith

theorem sum_Xs_le : ∑ l : Ln k q, (Xs L l).card ≤ 2 * k ^ 3 * q := by
  calc
    _ ≤ ∑ l : Ln k q, k * blen L l.2 := sum_le_sum fun l _ => card_Xs_le L l
    _ = k * ∑ l : Ln k q, blen L l.2 := (mul_sum ..).symm
    _ ≤ k * (2 * k ^ 2 * q) := Nat.mul_le_mul_left _ (sum_blen_axes_le L)
    _ = _ := by ring

/-- A global reserve-input bound; the logarithmic term remains explicit. -/
theorem total_need_le (lam : ℕ) :
    ∑ v, needAt L s lam v ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q := by
  rw [sum_needAt]
  simp only [laneBud]
  simp_rw [mul_add, add_mul, sum_add_distrib]
  simp_rw [← mul_sum, ← sum_mul]
  have hl := sum_blen_axes_le L
  have hx := sum_Xs_le L
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [card_Ln]
  simp_rw [← mul_sum]
  nlinarith [Nat.mul_le_mul_left (2 * s + 2 * k) hl,
    Nat.mul_le_mul_left (15 * lam + 1) hx]

theorem total_resv_le [NeZero n] (td : TDims n k s q) :
    ∑ Q, resv L n s Q ≤
      6 * k ^ 2 * q * s + (14 + 30 * GroupedOrder.lamN n) * k ^ 3 * q + 6 * k ^ 2 := by
  simp only [resv, Rneed, sum_add_distrib]
  rw [sum_regionSize (n := n) L td]
  have hn := total_need_le (s := s) L (GroupedOrder.lamN n)
  have hl := laneCells_bound (s := s) L
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  nlinarith

/-- Once the logarithmic batch slack fits in a square, the aggregate need is
linear in the reserved stripe inventory. -/
theorem total_need_coarse (lam : ℕ) (hks : k ≤ s) (hlam : k * lam ≤ s) :
    ∑ v, needAt L s lam v ≤ 48 * k ^ 2 * q * s := by
  have h := total_need_le (s := s) L lam
  nlinarith [Nat.mul_le_mul_left (k ^ 2 * q) hks,
    Nat.mul_le_mul_left (k ^ 2 * q) hlam]

theorem total_resv_coarse [NeZero n] (td : TDims n k s q)
    (hlam : k * GroupedOrder.lamN n ≤ s) :
    ∑ Q, resv L n s Q ≤ 56 * k ^ 2 * q * s := by
  have h := total_resv_le L td
  have hks : k ≤ s := by have := td.hd.room; omega
  have hs : 1 ≤ s := by have := td.hd.room; omega
  have hq : 1 ≤ q := by have := td.two_le_q; omega
  have hqs : 1 ≤ q * s := by nlinarith
  nlinarith [Nat.mul_le_mul_left (k ^ 2 * q) hks,
    Nat.mul_le_mul_left (k ^ 2 * q) hlam, Nat.mul_le_mul_left (k ^ 2) hqs]

set_option maxHeartbeats 800000 in
/-- Pure polynomial estimate, separated from the geometric definitions. -/
theorem polynomial_budget (k q s d lc nd rv : ℕ)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s) (hks : k ≤ s) (hkq : k * q ≤ s)
    (hlc : lc ≤ 2 * k ^ 2 * q * s) (hnd : nd ≤ 48 * k ^ 2 * q * s)
    (hrv : rv ≤ 56 * k ^ 2 * q * s) :
    2 * (k * s) + 52 * (k * s) * rv +
      runCost (k * s) k q s d lc nd +
      (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) +
          9354 * k ^ 2 * (k * s))) / 2 ≤
      100000 * (d + 1) * (k ^ 2 * s ^ 3) := by
  let V := k ^ 2 * q * s
  let X := k ^ 2 * s ^ 3
  have hv1 : 1 ≤ V := Nat.succ_le_of_lt (by dsimp [V]; positivity)
  have hqs : 1 ≤ q * s := by nlinarith
  have hkq1 : 1 ≤ k * q := by nlinarith
  have hnV : k * s ≤ V := by
    dsimp [V]
    nlinarith [Nat.mul_le_mul_left (k * s) hkq1]
  have hkV : k ^ 2 ≤ V := by
    dsimp [V]
    nlinarith [Nat.mul_le_mul_left (k ^ 2) hqs]
  have hVX : (k * s) * V ≤ X := by
    dsimp [V, X]
    nlinarith [Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hkq]
  have hnX : k * s ≤ X := by
    nlinarith [Nat.mul_le_mul_left (k * s) hv1]
  have hk2 : k ≤ k ^ 2 := by nlinarith
  have hp2 : k ^ 2 * s ^ 2 ≤ X := by
    dsimp [X]
    nlinarith [Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hs]
  have hp1 : k ^ 2 * s ≤ X := by
    have : k ^ 2 * s ≤ k ^ 2 * s ^ 2 := by
      nlinarith [Nat.mul_le_mul_left (k ^ 2 * s) hs]
    omega
  have hp0 : k ^ 2 ≤ X := by
    have := Nat.mul_le_mul_left (k ^ 2) hs
    omega
  have hpk : k ^ 3 * s ≤ X := by
    nlinarith [Nat.mul_le_mul_left (k ^ 2 * s) hks]
  have hfinish : k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) +
      9354 * k ^ 2 * (k * s) ≤ 20000 * X := by
    dsimp [X] at *
    nlinarith only [hp2, hp1, hp0, hpk]
  have hclean : 26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) ≤ 2990 * X := by
    have htot : (lc + (nd + (rv + lc))) + 2 * (k * s) + 5 ≤ 115 * V := by
      dsimp [V] at *
      nlinarith only [hlc, hnd, hrv, hnV, hv1]
    nlinarith [Nat.mul_le_mul_left (26 * (k * s)) htot]
  have hpre : 52 * (k * s) * rv ≤ 2912 * X := by
    have := Nat.mul_le_mul_left (52 * (k * s)) hrv
    dsimp [V] at hVX
    nlinarith
  have hhop : hopK k q s ≤ 3000 * s := by
    unfold hopK
    nlinarith
  have hmain : hopK k q s * (2 * d * (k * s) ^ 2) ≤ 6000 * d * X := by
    dsimp [X]
    nlinarith [Nat.mul_le_mul_right (2 * d * (k * s) ^ 2) hhop]
  have hjunk : lc * (k * s) ≤ 2 * X := by
    have := Nat.mul_le_mul_right (k * s) hlc
    dsimp [V] at hVX
    nlinarith
  have hstock : (k * s) * ((2 * d + 1) * nd) ≤ 48 * (2 * d + 1) * X := by
    have hb : (k * s) * nd ≤ 48 * X := by
      have := Nat.mul_le_mul_left (k * s) hnd
      dsimp [V] at hVX
      nlinarith
    nlinarith [Nat.mul_le_mul_left (2 * d + 1) hb]
  have hr1 : 3 * (s + 3) * (s ^ 2 * (15 * k ^ 2 + 30 * k + 18)) ≤ 756 * X := by
    have ha : 15 * k ^ 2 + 30 * k + 18 ≤ 63 * k ^ 2 := by nlinarith
    have hb : 3 * (s + 3) ≤ 12 * s := by omega
    have := Nat.mul_le_mul hb (Nat.mul_le_mul_left (s ^ 2) ha)
    dsimp [X]
    nlinarith
  have hr2 : 3 * (s + 3) * ((14 * k + 18) * (lc + k ^ 2)) ≤ 1152 * X := by
    have ha : 14 * k + 18 ≤ 32 * k := by omega
    have hb : lc + k ^ 2 ≤ 3 * V := by
      dsimp [V] at *
      nlinarith only [hlc, hkV]
    have hc : 3 * (s + 3) ≤ 12 * s := by omega
    have := Nat.mul_le_mul hc (Nat.mul_le_mul ha hb)
    nlinarith
  have hrun : runCost (k * s) k q s d lc nd ≤ (1958 + 6096 * d) * X := by
    unfold runCost
    nlinarith only [hjunk, hmain, hstock, hr1, hr2]
  have hdiv := Nat.div_le_self (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
    (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s))) 2
  change _ ≤ 100000 * (d + 1) * X
  nlinarith only [hdiv, hrun, hfinish, hclean, hpre, hnX, Nat.zero_le (d * X), Nat.zero_le X]

/-- The certified tree algorithm has the desired local-work scale when lane
width and logarithmic slack fit in the fine squares. -/
theorem treeBound_le [NeZero n] (td : TDims n k s q)
    (hkq : k * q ≤ s) (hlam : k * GroupedOrder.lamN n ≤ s) :
    treeBound L n s ≤ 100000 * (L.depth + 1) * (k ^ 2 * s ^ 3) := by
  have hn := td.mul
  subst n
  apply polynomial_budget
  · have := td.hd.two_le; omega
  · have := td.two_le_q; omega
  · have := td.hd.room; omega
  · have := td.hd.room; omega
  · exact hkq
  · exact laneCells_bound L
  · exact total_need_coarse L _ (by have := td.hd.room; omega) hlam
  · exact total_resv_coarse L td hlam

end SlidingPuzzle.Tree
