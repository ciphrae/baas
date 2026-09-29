import SlidingPuzzle.Tree.AsympAccounting

/-! # Sharper accounting for the tree algorithm

Once `8kq ≤ s`, `16kλ ≤ s` and `2048·depth·k ≤ s`, the certified bound is at most
`50 (depth + 3) k² s³`. The main terms are the hops (`40·depth`), the relocations
(`≈ 45`), the preload (`≈ 51`) and the cleanup (`≈ 29`). -/
namespace SlidingPuzzle.Tree
open Finset

namespace Fine

/-! Elementary monomial bounds against `X = k² s³`. -/

theorem f1 {k q s : ℕ} (hkq : 8 * k * q ≤ s) : 8 * (k ^ 3 * q * s ^ 2) ≤ k ^ 2 * s ^ 3 := by
  have := Nat.mul_le_mul_right (k ^ 2 * s ^ 2) hkq
  calc 8 * (k ^ 3 * q * s ^ 2) = 8 * k * q * (k ^ 2 * s ^ 2) := by ring
    _ ≤ s * (k ^ 2 * s ^ 2) := this
    _ = _ := by ring

theorem f2 {k q s lam : ℕ} (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s) :
    128 * (lam * k ^ 4 * q * s) ≤ k ^ 2 * s ^ 3 := by
  have := Nat.mul_le_mul_right (k ^ 2 * s) (Nat.mul_le_mul hkl hkq)
  calc 128 * (lam * k ^ 4 * q * s) = 16 * k * lam * (8 * k * q) * (k ^ 2 * s) := by ring
    _ ≤ s * s * (k ^ 2 * s) := this
    _ = _ := by ring

theorem f3 {k q s : ℕ} (hkq : 8 * k * q ≤ s) (hks : 2048 * k ≤ s) :
    16384 * (k ^ 4 * q * s) ≤ k ^ 2 * s ^ 3 := by
  have := Nat.mul_le_mul_right (k ^ 2 * s) (Nat.mul_le_mul hks hkq)
  calc 16384 * (k ^ 4 * q * s) = 2048 * k * (8 * k * q) * (k ^ 2 * s) := by ring
    _ ≤ s * s * (k ^ 2 * s) := this
    _ = _ := by ring

theorem f4 {k s d : ℕ} (hdk : 2048 * d * k ≤ s) : 2048 * (d * k ^ 3 * s ^ 2) ≤ k ^ 2 * s ^ 3 := by
  have := Nat.mul_le_mul_right (k ^ 2 * s ^ 2) hdk
  calc 2048 * (d * k ^ 3 * s ^ 2) = 2048 * d * k * (k ^ 2 * s ^ 2) := by ring
    _ ≤ s * (k ^ 2 * s ^ 2) := this
    _ = _ := by ring

theorem f5 {k s d : ℕ} (hk : 256 ≤ k) (hdk : 2048 * d * k ≤ s) :
    524288 * (d * (k ^ 2 * s ^ 2)) ≤ k ^ 2 * s ^ 3 := by
  have h := f4 hdk
  have := Nat.mul_le_mul_right (d * k ^ 2 * s ^ 2) hk
  calc 524288 * (d * (k ^ 2 * s ^ 2)) = 2048 * (256 * (d * k ^ 2 * s ^ 2)) := by ring
    _ ≤ 2048 * (k * (d * k ^ 2 * s ^ 2)) := Nat.mul_le_mul_left _ this
    _ = 2048 * (d * k ^ 3 * s ^ 2) := by ring
    _ ≤ _ := h

theorem f6 {k s : ℕ} (hk : 1 ≤ k) (hks : 2048 * k ≤ s) : 2048 * (k ^ 3 * s) ≤ k ^ 2 * s ^ 3 := by
  have h1 := Nat.mul_le_mul_right (k ^ 2 * s) hks
  have hs : 1 ≤ s := by omega
  have h2 : k ^ 2 * s * s ≤ k ^ 2 * s ^ 3 := by
    calc k ^ 2 * s * s = k ^ 2 * s * s * 1 := by ring
      _ ≤ k ^ 2 * s * s * s := Nat.mul_le_mul_left _ hs
      _ = _ := by ring
  calc 2048 * (k ^ 3 * s) = 2048 * k * (k ^ 2 * s) := by ring
    _ ≤ s * (k ^ 2 * s) := h1
    _ = k ^ 2 * s * s := by ring
    _ ≤ _ := h2

theorem f7 {k s : ℕ} (hs : 2048 ≤ s) : 2048 * (k ^ 2 * s ^ 2) ≤ k ^ 2 * s ^ 3 := by
  have := Nat.mul_le_mul_left (k ^ 2 * s ^ 2) hs
  calc 2048 * (k ^ 2 * s ^ 2) = k ^ 2 * s ^ 2 * 2048 := by ring
    _ ≤ k ^ 2 * s ^ 2 * s := this
    _ = _ := by ring

theorem f8 {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) : k * s ≤ k ^ 2 * s ^ 2 := by
  have : 1 ≤ k * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc k * s = k * s * 1 := by ring
    _ ≤ k * s * (k * s) := Nat.mul_le_mul_left _ this
    _ = _ := by ring

/-! The terms of the certified bound. -/

theorem nd_term {k q s lam nd : ℕ} (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s)
    (hks : 2048 * k ≤ s)
    (hnd : nd ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q) :
    (k * s) * nd ≤ k ^ 2 * s ^ 3 := by
  have h := Nat.mul_le_mul_left (k * s) hnd
  have e : (k * s) * (4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q) =
      4 * (k ^ 3 * q * s ^ 2) + 14 * (k ^ 4 * q * s) + 30 * (lam * k ^ 4 * q * s) := by ring
  have := f1 hkq; have := f2 hkq hkl; have := f3 hkq hks
  omega

theorem rv_term {k q s lam rv : ℕ} (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s)
    (hk : 1 ≤ k) (hks : 2048 * k ≤ s)
    (hrv : rv ≤ 6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :
    (k * s) * rv ≤ k ^ 2 * s ^ 3 := by
  have h := Nat.mul_le_mul_left (k * s) hrv
  have e : (k * s) * (6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) =
      6 * (k ^ 3 * q * s ^ 2) + 14 * (k ^ 4 * q * s) + 30 * (lam * k ^ 4 * q * s) +
        6 * (k ^ 3 * s) := by ring
  have := f1 hkq; have := f2 hkq hkl; have := f3 hkq hks; have := f6 hk hks
  omega

theorem lc_term {k q s lc : ℕ} (hkq : 8 * k * q ≤ s) (hlc : lc ≤ 2 * k ^ 2 * q * s) :
    4 * ((k * s) * lc) ≤ k ^ 2 * s ^ 3 := by
  have h := Nat.mul_le_mul_left (k * s) hlc
  have e : (k * s) * (2 * k ^ 2 * q * s) = 2 * (k ^ 3 * q * s ^ 2) := by ring
  have := f1 hkq
  omega

theorem clean_term {k q s lam lc nd rv : ℕ} (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s)
    (hk : 1 ≤ k) (hks : 2048 * k ≤ s) (hlc : lc ≤ 2 * k ^ 2 * q * s)
    (hnd : nd ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q)
    (hrv : rv ≤ 6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :
    26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) ≤ 60 * (k ^ 2 * s ^ 3) := by
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hlc hnd) hrv) hlc
  have h := Nat.mul_le_mul_left (26 * (k * s)) hsum
  have e1 : 26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) =
      26 * (k * s) * (lc + nd + rv + lc) + 52 * (k ^ 2 * s ^ 2) + 130 * (k * s) := by ring
  have e2 : 26 * (k * s) * (2 * k ^ 2 * q * s + (4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q) +
      (6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) + 2 * k ^ 2 * q * s) =
      364 * (k ^ 3 * q * s ^ 2) + 728 * (k ^ 4 * q * s) + 1560 * (lam * k ^ 4 * q * s) +
        156 * (k ^ 3 * s) := by ring
  have := f1 hkq; have := f2 hkq hkl; have := f3 hkq hks; have := f6 hk hks
  have := f7 (k := k) (show 2048 ≤ s by omega); have := f8 hk (show 1 ≤ s by omega)
  omega

theorem fin_term {k s : ℕ} (hk : 1 ≤ k) (hks : 2048 * k ≤ s) :
    k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s) ≤
      6 * (k ^ 2 * s ^ 3) := by
  have hs : 2048 ≤ s := by omega
  have hs2 : 2048 * s ≤ s * s := Nat.mul_le_mul_right s hs
  have hs3 : 2048 * (s * s) ≤ s * s * s := by
    have := Nat.mul_le_mul_left (s * s) hs; linarith
  have hks2 : 2048 * (k * s) ≤ s * s := by
    have := Nat.mul_le_mul_right s hks; linarith
  have h1 : 1509 * (s * s) + 1505 * s + 4796 + 9354 * (k * s) ≤ s * s * s := by omega
  have h2 := Nat.mul_le_mul_left (k ^ 2) h1
  have e1 : k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s) =
      5 * (k ^ 2 * s ^ 3) + k ^ 2 * (1509 * (s * s) + 1505 * s + 4796 + 9354 * (k * s)) := by ring
  have e2 : k ^ 2 * (s * s * s) = k ^ 2 * s ^ 3 := by ring
  omega

theorem hop_term {k q s d : ℕ} (hk : 256 ≤ k) (hkq : 8 * k * q ≤ s) (hdk : 2048 * d * k ≤ s) :
    hopK k q s * (2 * d * (k * s) ^ 2) ≤ 45 * d * (k ^ 2 * s ^ 3) + 2 * (k ^ 2 * s ^ 3) := by
  unfold hopK
  have e : (20 * s + 20 * k * (q + 2) + 600 * k + 2000) * (2 * d * (k * s) ^ 2) =
      40 * d * (k ^ 2 * s ^ 3) + 5 * d * (8 * (k ^ 3 * q * s ^ 2)) +
        1280 * (d * k ^ 3 * s ^ 2) + 4000 * (d * (k ^ 2 * s ^ 2)) := by ring
  have g1 := Nat.mul_le_mul_left (5 * d) (f1 hkq)
  have e1 : 5 * d * (k ^ 2 * s ^ 3) = 5 * (d * (k ^ 2 * s ^ 3)) := by ring
  have e2 : 45 * d * (k ^ 2 * s ^ 3) = 45 * (d * (k ^ 2 * s ^ 3)) := by ring
  have e3 : 40 * d * (k ^ 2 * s ^ 3) = 40 * (d * (k ^ 2 * s ^ 3)) := by ring
  have := f4 hdk; have := f5 hk hdk
  omega

theorem stock_term {k s d nd : ℕ} (h : (k * s) * nd ≤ k ^ 2 * s ^ 3) :
    (k * s) * ((2 * d + 1) * nd) ≤ (2 * d + 1) * (k ^ 2 * s ^ 3) := by
  calc (k * s) * ((2 * d + 1) * nd) = (2 * d + 1) * ((k * s) * nd) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h

theorem r1_term {k s : ℕ} (hk : 256 ≤ k) (hs : 342 ≤ s) :
    3 * (s + 3) * (s ^ 2 * (15 * k ^ 2 + 30 * k + 18)) ≤ 46 * (k ^ 2 * s ^ 3) := by
  have hb : 3 * (s + 3) * 76 ≤ 230 * s := by
    have e : 3 * (s + 3) * 76 = 228 * s + 684 := by ring
    omega
  have ha : 5 * (15 * k ^ 2 + 30 * k + 18) ≤ 76 * k ^ 2 := by
    clear hb
    have := Nat.mul_le_mul_right k hk
    have e : k ^ 2 = k * k := by ring
    rw [e]; omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 5 by norm_num)
  calc 5 * (3 * (s + 3) * (s ^ 2 * (15 * k ^ 2 + 30 * k + 18)))
      = 3 * (s + 3) * s ^ 2 * (5 * (15 * k ^ 2 + 30 * k + 18)) := by ring
    _ ≤ 3 * (s + 3) * s ^ 2 * (76 * k ^ 2) := Nat.mul_le_mul_left _ ha
    _ = 3 * (s + 3) * 76 * (s ^ 2 * k ^ 2) := by ring
    _ ≤ 230 * s * (s ^ 2 * k ^ 2) := Nat.mul_le_mul_right _ hb
    _ = 5 * (46 * (k ^ 2 * s ^ 3)) := by ring

theorem r2_term {k q s lc : ℕ} (hk : 256 ≤ k) (hkq : 8 * k * q ≤ s) (hks : 2048 * k ≤ s)
    (hlc : lc ≤ 2 * k ^ 2 * q * s) :
    3 * (s + 3) * ((14 * k + 18) * (lc + k ^ 2)) ≤ 11 * (k ^ 2 * s ^ 3) := by
  have ha : 3 * (s + 3) * (14 * k + 18) ≤ 43 * (k * s) := by
    have h1 := Nat.mul_le_mul_right s hk
    have h2 := Nat.mul_le_mul_right k (show 342 ≤ s by omega)
    have e : 3 * (s + 3) * (14 * k + 18) = 42 * (k * s) + 54 * s + 126 * k + 162 := by ring
    have e2 : s * k = k * s := by ring
    omega
  have hb : lc + k ^ 2 ≤ 2 * k ^ 2 * q * s + k ^ 2 := by omega
  have h := Nat.mul_le_mul ha hb
  have e1 : 3 * (s + 3) * ((14 * k + 18) * (lc + k ^ 2)) =
      3 * (s + 3) * (14 * k + 18) * (lc + k ^ 2) := by ring
  have e2 : 43 * (k * s) * (2 * k ^ 2 * q * s + k ^ 2) =
      86 * (k ^ 3 * q * s ^ 2) + 43 * (k ^ 3 * s) := by ring
  have := f1 hkq; have := f6 (by omega) hks
  omega

end Fine

variable {n k s q : ℕ} (L : LaneSys k q)

open Fine in
/-- Pure polynomial estimate with the reserve inputs kept exact. -/
theorem polynomial_budget_fine (k q s d lam lc nd rv : ℕ)
    (hk : 256 ≤ k) (hd : 1 ≤ d)
    (hkq : 8 * k * q ≤ s) (hkl : 16 * k * lam ≤ s) (hdk : 2048 * d * k ≤ s)
    (hlc : lc ≤ 2 * k ^ 2 * q * s)
    (hnd : nd ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q)
    (hrv : rv ≤ 6 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q + 6 * k ^ 2) :
    2 * (k * s) + 52 * (k * s) * rv +
      runCost (k * s) k q s d lc nd +
      (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
        (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) +
          9354 * k ^ 2 * (k * s))) / 2 ≤
      50 * (d + 3) * (k ^ 2 * s ^ 3) := by
  have hks : 2048 * k ≤ s := le_trans (Nat.mul_le_mul_right k (by omega)) hdk
  have hk1 : 1 ≤ k := by omega
  have Pnd := nd_term hkq hkl hks hnd
  have Prv := rv_term hkq hkl hk1 hks hrv
  have Plc := lc_term hkq hlc
  have Pcl := clean_term hkq hkl hk1 hks hlc hnd hrv
  have Pfin := fin_term hk1 hks
  have Phop := hop_term hk hkq hdk
  have Pst := stock_term (d := d) Pnd
  have Pr1 := r1_term hk (show 342 ≤ s by omega)
  have Pr2 := r2_term hk hkq hks hlc
  have P1 := f6 hk1 hks
  have P2 : k * s ≤ k ^ 3 * s := Nat.mul_le_mul_right _ (by nlinarith)
  unfold runCost
  generalize k ^ 2 * s ^ 3 = X at *
  have Pdiv : (26 * (k * s) * ((lc + (nd + (rv + lc))) + 2 * (k * s) + 5) +
      (k ^ 2 * (5 * s ^ 3 + 1509 * s ^ 2 + 1505 * s + 4796) + 9354 * k ^ 2 * (k * s))) / 2 ≤
      33 * X := by
    apply Nat.div_le_of_le_mul; omega
  have e1 : 52 * (k * s) * rv = 52 * ((k * s) * rv) := by ring
  have e2 : lc * (k * s) = (k * s) * lc := by ring
  have e3 : 3 * (s + 3) * (s ^ 2 * (15 * k ^ 2 + 30 * k + 18) + (14 * k + 18) * (lc + k ^ 2)) =
      3 * (s + 3) * (s ^ 2 * (15 * k ^ 2 + 30 * k + 18)) +
        3 * (s + 3) * ((14 * k + 18) * (lc + k ^ 2)) := by ring
  have e4 : 50 * (d + 3) * X = 50 * (d * X) + 150 * X := by ring
  have e5 : 45 * d * X = 45 * (d * X) := by ring
  have e6 : (2 * d + 1) * X = 2 * (d * X) + X := by ring
  omega

/-- The certified tree bound is `O(depth · k² s³)` with small constants once lane width
and logarithmic slack are small against the square side. -/
theorem treeBound_le_fine [NeZero n] (td : TDims n k s q) (hk : 256 ≤ k) (hd : 1 ≤ L.depth)
    (hkq : 8 * k * q ≤ s) (hlam : 16 * k * GroupedOrder.lamN n ≤ s)
    (hdk : 2048 * L.depth * k ≤ s) :
    treeBound L n s ≤ 50 * (L.depth + 3) * (k ^ 2 * s ^ 3) := by
  have hn := td.mul
  subst n
  apply polynomial_budget_fine k q s L.depth _ _ _ _ hk hd hkq hlam hdk
  · exact laneCells_bound L
  · exact total_need_le L _
  · exact total_resv_le L td

end SlidingPuzzle.Tree
