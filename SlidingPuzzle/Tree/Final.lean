import SlidingPuzzle.Tree.FineAccounting
import SlidingPuzzle.Tree.AsympBound
import SlidingPuzzle.Tree.Feasibility
import SlidingPuzzle.Tree.ReserveAccounting

/-! # The tree bound for a lane system

Feasibility of every hypothesis of the tree algorithm from `8k²q ≤ n`,
`256h ≤ q ≤ k` and `2λ ≤ q` (`optimalLength_le_lanes`). -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

/-- Pure arithmetic: the reserve of a square fits in the free part of its region. -/
theorem fit_arith (k q s d lam : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) (hs : 100 ≤ s)
    (h1 : 8 * k * q ≤ s) (h2 : 16 * k * lam ≤ s) (h3 : 64 * d * k ≤ s) :
    2 * ((2 * s + 2 * k + (15 * lam + 1) * k) * (2 * d * k) + 4 * k * q) +
      (s ^ 2 - (s - q) * (s - q)) + 6 + 2 ≤ (s - q) * (s - q) := by
  have hqs : 8 * q ≤ s := by nlinarith
  have hks : 16 * k ≤ s := by nlinarith
  have hF : 2 * s + 2 * k + (15 * lam + 1) * k ≤ 4 * s := by
    have : (15 * lam + 1) * k = 15 * (k * lam) + k := by ring
    rw [this]; nlinarith
  have hT1 : (2 * s + 2 * k + (15 * lam + 1) * k) * (2 * d * k) ≤ 4 * s * (2 * d * k) :=
    Nat.mul_le_mul_right _ hF
  have hT2 : 4 * s * (2 * d * k) * 8 ≤ s * s := by
    have : 8 * (4 * s * (2 * d * k)) = s * (64 * d * k) := by ring
    nlinarith [Nat.mul_le_mul_left s h3]
  have hkq : 4 * k * q ≤ s := by nlinarith
  obtain ⟨r, rfl⟩ : ∃ r, s = q + r := ⟨s - q, by omega⟩
  have e1 : (q + r) ^ 2 - (q + r - q) * (q + r - q) = 2 * q * r + q * q := by
    rw [Nat.add_sub_cancel_left]
    have : (q + r) ^ 2 = 2 * q * r + q * q + r * r := by ring
    omega
  rw [e1, Nat.add_sub_cancel_left]
  nlinarith

variable {n k s q : ℕ} (L : LaneSys k q)

theorem hfit_of_grid [NeZero n] (td : TDims n k s q) (hs : 100 ≤ s)
    (h1 : 8 * k * q ≤ s) (h2 : 16 * k * GroupedOrder.lamN n ≤ s)
    (h3 : 64 * L.depth * k ≤ s) (Q : Sq k) :
    resv L n s Q + 2 ≤ (s - q) * (s - q) := by
  have hk : 1 ≤ k := by have := td.hd.two_le; omega
  have hf := fit_arith k q s L.depth (GroupedOrder.lamN n) hk td.two_le_q hs h1 h2 h3
  have hn := needAt_le L s (GroupedOrder.lamN n) Q
  have hr := regionSize_ge (n := n) L td Q
  have hsub : s ^ 2 - regionSize (n := n) L s Q ≤ s ^ 2 - (s - q) * (s - q) :=
    Nat.sub_le_sub_left hr _
  unfold resv Rneed
  omega

open SlidingPuzzle in
/-- The tree bound for any lane system of depth `h` on `k` blocks with `q` offsets, once
`8 k² q ≤ n`, `256 h ≤ q ≤ k` and `2 λ ≤ q`. -/
theorem optimalLength_le_lanes {n k q h : ℕ} [NeZero n] (L : LaneSys k q) (hd : L.depth = h)
    (hh : 1 ≤ h) (hke : Even k) (hqe : Even q) (hqk : q ≤ k) (hk : 256 ≤ k)
    (hqh : 256 * h ≤ q) (hlam : 2 * GroupedOrder.lamN n ≤ q) (hlo : 8 * k * q * k ≤ n)
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * k) +
      2 * (50 * (h + 3) * k ^ 2 * (n / k) ^ 3) := by
  set s := n / k with hs
  have hsq : 8 * k * q ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le (by omega)]; exact hlo
  have hks : 2048 * h * k ≤ s := by
    have : 2048 * h * k ≤ 8 * k * q := by
      have := Nat.mul_le_mul_left (8 * k) hqh
      have e : 8 * k * (256 * h) = 2048 * h * k := by ring
      omega
    omega
  have hn' : k * s ≤ n := Nat.mul_div_le n k
  have hk2048 : 2048 * k ≤ s := le_trans (Nat.mul_le_mul_right k (by nlinarith)) hks
  have hdim : TDims (k * s) k s q := by
    refine ⟨⟨by omega, hke, by omega, rfl, by omega⟩, by omega, hqe, hqk⟩
  have hlam2 : 2 * GroupedOrder.lamN (k * s) ≤ q := by
    have : GroupedOrder.lamN (k * s) ≤ GroupedOrder.lamN n := by
      unfold GroupedOrder.lamN
      have := Nat.log_mono_right (b := 2) hn'
      omega
    omega
  have h16 : 16 * k * GroupedOrder.lamN (k * s) ≤ s := by
    have h2 := Nat.mul_le_mul_left (8 * k) hlam2
    have e : 16 * k * GroupedOrder.lamN (k * s) = 8 * k * (2 * GroupedOrder.lamN (k * s)) := by ring
    omega
  have h64 : 64 * L.depth * k ≤ s := by
    rw [hd]
    have : 64 * h * k ≤ 2048 * h * k := Nat.mul_le_mul_right k (by omega)
    omega
  have hs100 : 100 ≤ s := by nlinarith
  have : NeZero (k * s) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hfit := hfit_of_grid L hdim hs100 hsq h16 h64
  have hev := event_bounds hdim hsq
  have hcap : 76 * k * GroupedOrder.lamN (k * s) ≤ 5 * s :=
    calc 76 * k * GroupedOrder.lamN (k * s) ≤ 80 * k * GroupedOrder.lamN (k * s) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 5 * (16 * k * GroupedOrder.lamN (k * s)) := by ring
      _ ≤ 5 * s := by omega
  have hres := optimalLength_le_tree_residual (n := n) (k := k) (q := q)
    (la := GroupedOrder.lamN (k * s)) L hdim hfit hcap hev.1 hev.2 B
  have htb := treeBound_le_fine L hdim hk (by rw [hd]; exact hh) hsq h16 (by rw [hd]; exact hks)
  rw [hd] at htb
  have hrem : n - k * (n / k) ≤ k := by
    have := Nat.mod_lt n (show 0 < k by omega)
    have := Nat.mod_add_div n k
    omega
  have hres' : optimalLength B ≤ manhattan B.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * (n - k * s)) + 2 * treeBound L (k * s) s := hres
  have hm' : (15 * n ^ 2 + 3002 * n + 1) * (n - k * s) ≤ (15 * n ^ 2 + 3002 * n + 1) * k :=
    Nat.mul_le_mul_left _ hrem
  have hfinal : optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * k) +
      2 * (50 * (h + 3) * (k ^ 2 * s ^ 3)) :=
    hres'.trans (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm') _)
      (Nat.mul_le_mul_left 2 htb))
  calc optimalLength B ≤ _ := hfinal
    _ = _ := by rw [hs]; ring

end SlidingPuzzle.Tree
