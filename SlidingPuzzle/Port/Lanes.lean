import SlidingPuzzle.Port.Budget
import SlidingPuzzle.Port.Tight
import SlidingPuzzle.Tree.AsympBound
import SlidingPuzzle.Tree.Final
import SlidingPuzzle.Tree.FinalLog
import SlidingPuzzle.Tree.LamGrid

/-! # The port bound for a tight lane system, on a board of any side

Parberry's prefix reduces the side `n` to `k·(n/k)`, where the port algorithm runs. For a
tight lane system of depth `h`, the cost is `1040 k² (n/k)³` once `n` exceeds `k²` times
`8q`, `16λ`, `14(q+2)`, and `(n/k)` exceeds `128(2h+1)q` and `2h·hopKc`, and `σ²` exceeds the reserve of a square. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle
open SlidingPuzzle.Tree

/-- The reserve fits in the free part of a region, for a tight lane system: no depth needed. -/
theorem hfit_tight {n k s q : ℕ} [NeZero n] (L : LaneSys k q) (hT : L.Tight) (td : TDims n k s q)
    (hkq : 8 * k * q ≤ s) (hkl : 16 * k * GroupedOrder.lamN n ≤ s) (hks : 1024 * k ≤ s)
    (Q : Hub.Sq k) : resv L n s Q + 2 ≤ (s - q) * (s - q) := by
  have hn := needAt_le_tight L hT s (GroupedOrder.lamN n) Q
  have hr := regionSize_ge (n := n) L td Q
  have hqs : q ≤ s := by have := td.q_lt_s; omega
  have hqk := td.q_le
  have hk2 := td.hd.two_le
  have h16q : 16 * q ≤ s := by
    have : 16 * q ≤ 8 * k * q := by nlinarith
    omega
  set lam := GroupedOrder.lamN n
  obtain ⟨r, rfl⟩ : ∃ r, s = q + r := ⟨s - q, by omega⟩
  have e1 : (q + r) ^ 2 - (q + r - q) * (q + r - q) = 2 * q * r + q * q := by
    rw [Nat.add_sub_cancel_left]
    have : (q + r) ^ 2 = 2 * q * r + q * q + r * r := by ring
    omega
  have hsub : (q + r) ^ 2 - regionSize (n := n) L (q + r) Q ≤ 2 * q * r + q * q := by
    rw [← e1]; exact Nat.sub_le_sub_left hr _
  unfold resv Rneed
  rw [Nat.add_sub_cancel_left]
  have hk1 : 1 ≤ k := by have := td.hd.two_le; omega
  -- `r ≥ 1016 k`, `r ≥ 63 q`
  have hr1 : 1016 * k ≤ r := by omega
  have hq8 : 8 * q ≤ r := by omega
  have hlr : 16 * k * lam ≤ q + r := hkl
  have a1 : 2 * ((2 * (q + r) + 2 * k + (15 * lam + 1) * k) * (2 * k) + 4 * k * q) =
      8 * (q + r) * k + 8 * k * k + 60 * (k * lam) * k + 4 * k * k + 8 * k * q := by ring
  have b1 : 60 * (k * lam) * k * 16 ≤ 60 * (q + r) * k := by
    have := Nat.mul_le_mul_left (60 * k) hlr
    nlinarith
  have b2 : 8 * (q + r) * k * 64 ≤ r * r := by nlinarith
  have b3 : 12 * k * k * 1024 ≤ r * r := by nlinarith
  have b4 : 8 * k * q * 8 ≤ r * r := by nlinarith
  have b5 : (2 * q * r + q * q) * 4 ≤ r * r := by nlinarith
  nlinarith

/-- Prefix plus port construction on the residual board. -/
theorem optimalLength_le_port_residual {n k q σ la : ℕ} [NeZero n] (L : LaneSys k q)
    (pd : PDims (k * (n / k)) k (n / k) q σ) (h8 : 8 ≤ σ)
    (hσ2 : ∀ Q, needAt L (n / k) (GroupedOrder.lamN (k * (n / k))) Q + 2 ≤ σ ^ 2)
    (hfit : ∀ Q, resv L (k * (n / k)) (n / k) Q + 2 ≤ ((n / k) - q) * ((n / k) - q))
    (hcap : 76 * k * la ≤ 5 * (n / k))
    (hcA : 2 * (4 * k ^ 2 * q * k * (n / k) ^ 2) ≤ 2 ^ la)
    (hcB : 2 * (4 * k ^ 2 * q * k ^ 2 * (n / k) ^ 2) <
      2 ^ GroupedOrder.lamN (k * (n / k)))
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * (n - k * (n / k))) +
      2 * portBound L (k * (n / k)) (n / k) σ := by
  have td := pd.td
  have hmn : k * (n / k) ≤ n := Nat.mul_div_le n k
  have hroom := td.hd.room
  have hk2 := td.hd.two_le
  have hm4 : 4 ≤ k * (n / k) := by
    calc 4 ≤ n / k := by omega
      _ ≤ k * (n / k) := Nat.le_mul_of_pos_left _ (by omega)
  let : NeZero (k * (n / k)) := ⟨by omega⟩
  obtain ⟨C, p, hp, hC⟩ := Parberry.exists_prefix B.val (n - k * (n / k)) (by omega)
  have hdn : n - k * (n / k) + k * (n / k) = n := Nat.sub_add_cancel hmn
  obtain ⟨A, hA⟩ := exists_residual_board (n - k * (n / k)) hdn C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hreachA : Reachable A :=
    residual_reachable (by omega : 2 ≤ k * (n / k)) (n - k * (n / k)) hdn C hC A hA hreachC
  obtain ⟨qpath, hq⟩ := exists_port_solution L pd h8 hσ2 hfit hcap hcA hcB A hreachA
  have hlen := qpath.length_add_manhattan
  have hzero : manhattan (target (k * (n / k))) = 0 := by simp [manhattan]
  have hq' : qpath.length ≤ manhattan A + 2 * portBound L (k * (n / k)) (n / k) σ := by
    omega
  have h := optimalLength_le_prefix_residual_solution B (n - k * (n / k)) hdn C p hC A hA qpath hq'
  omega

/-- The port bound for a tight lane system of depth `h`: `190 k² (n/k)³ + 780 k³ q (n/k)²` plus
the cheap hops. -/
theorem optimalLength_le_port_lanes {n k q h σ : ℕ} [NeZero n] (L : LaneSys k q) (hT : L.Tight)
    (hd : L.depth = h) (hh : 1 ≤ h) (hke : Even k) (hqe : Even q) (hq2 : 2 ≤ q) (hqk : q ≤ k)
    (hk : 64 ≤ k) (hl : 64 ≤ GroupedOrder.lamN n)
    (hlo : 8 * k * q * k ≤ n) (hlo2 : 16 * k * GroupedOrder.lamN n * k ≤ n)
    (hhk : 2 * h + 1 ≤ k)
    (h9 : 9 * σ * k ≤ n) (h8 : 8 ≤ σ)
    (hσ : 2 * ((2 * (n / k) + 2 * k + (15 * GroupedOrder.lamN n + 1) * k) * (2 * k) + 4 * k * q)
      + 2 ≤ σ ^ 2)
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * k) +
      2 * (190 * (k ^ 2 * (n / k) ^ 3) + 780 * (k ^ 3 * q * (n / k) ^ 2) +
        hopKc k σ * (2 * h * (k * (n / k)) ^ 2)) := by
  set s := n / k with hs
  have hk0 : 0 < k := by omega
  have hdiv : ∀ {a : ℕ}, a * k ≤ n → a ≤ s := fun h => by
    rw [hs, Nat.le_div_iff_mul_le hk0]; exact h
  have hsq : 8 * k * q ≤ s := hdiv hlo
  have hsl : 16 * k * GroupedOrder.lamN n ≤ s := hdiv hlo2
  have hsph : 8 * (2 * h + 1) * q ≤ s := by
    have := Nat.mul_le_mul_left (8 * q) hhk
    have e : 8 * q * (2 * h + 1) = 8 * (2 * h + 1) * q := by ring
    have e2 : 8 * q * k = 8 * k * q := by ring
    omega
  have hs9 : 9 * σ ≤ s := hdiv h9
  have hn' : k * s ≤ n := Nat.mul_div_le n k
  have hks : 1024 * k ≤ s := by
    have : 1024 * k ≤ 16 * k * GroupedOrder.lamN n := by
      have := Nat.mul_le_mul_left (16 * k) hl
      calc 1024 * k = 16 * k * 64 := by ring
        _ ≤ _ := this
    omega
  have hdim : TDims (k * s) k s q := by
    refine ⟨⟨by omega, hke, by omega, rfl, by omega⟩, by omega, hqe, hqk⟩
  have hfitσ : 2 * σ + 2 * k + 8 ≤ s := by omega
  have pd : PDims (k * s) k s q σ := ⟨hdim, by omega, hfitσ⟩
  have hlam_le : GroupedOrder.lamN (k * s) ≤ GroupedOrder.lamN n := lamN_mono hn'
  have hks22 : 2 ^ 21 ≤ k * s := by
    have h1 : 64 * (1024 * 64) ≤ k * s := Nat.mul_le_mul hk (le_trans (by omega) hks)
    calc 2 ^ 21 ≤ 64 * (1024 * 64) := by norm_num
      _ ≤ _ := h1
  have hl' : 64 ≤ GroupedOrder.lamN (k * s) :=
    le_trans (by norm_num) (lamN_ge_of_pow hks22)
  have h16 : 16 * k * GroupedOrder.lamN (k * s) ≤ s :=
    le_trans (Nat.mul_le_mul_left _ hlam_le) hsl
  have : NeZero (k * s) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hfit := hfit_tight L hT hdim hsq h16 (by omega)
  have hev := event_bounds hdim hsq
  have hcap : 76 * k * GroupedOrder.lamN (k * s) ≤ 5 * s :=
    calc 76 * k * GroupedOrder.lamN (k * s) ≤ 80 * k * GroupedOrder.lamN (k * s) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 5 * (16 * k * GroupedOrder.lamN (k * s)) := by ring
      _ ≤ 5 * s := by omega
  have hσ2 : ∀ Q, needAt L s (GroupedOrder.lamN (k * s)) Q + 2 ≤ σ ^ 2 := by
    intro Q
    have h1 := needAt_le_tight L hT s (GroupedOrder.lamN (k * s)) Q
    have h2 : 2 * ((2 * s + 2 * k + (15 * GroupedOrder.lamN (k * s) + 1) * k) * (2 * k) +
        4 * k * q) ≤ 2 * ((2 * s + 2 * k + (15 * GroupedOrder.lamN n + 1) * k) * (2 * k) +
        4 * k * q) := by
      have := Nat.mul_le_mul_right k (Nat.add_le_add_right (Nat.mul_le_mul_left 15 hlam_le) 1)
      have := Nat.mul_le_mul_right (2 * k) (Nat.add_le_add_left this (2 * s + 2 * k))
      omega
    omega
  have hres := optimalLength_le_port_residual (n := n) (k := k) (q := q) (σ := σ)
    (la := GroupedOrder.lamN (k * s)) L pd (by omega) hσ2 hfit hcap hev.1 hev.2 B
  have hbud := port_budget3 k q s h (GroupedOrder.lamN (k * s)) σ (laneCells L s)
    (∑ v, needAt L s (GroupedOrder.lamN (k * s)) v) (∑ Q, resv L (k * s) s Q)
    (by omega) hl' hsq h16 (by omega) hsph hs9 (laneCells_bound L) (total_need_le L _)
    (total_resv_le L hdim)
  have hpb : portBound L (k * s) s σ ≤ 190 * (k ^ 2 * s ^ 3) + 780 * (k ^ 3 * q * s ^ 2) +
      hopKc k σ * (2 * h * (k * s) ^ 2) := by
    unfold portBound
    rw [hd]
    exact hbud
  have hrem : n - k * (n / k) ≤ k := by
    have := Nat.mod_lt n (show 0 < k by omega)
    have := Nat.mod_add_div n k
    omega
  have hm' : (15 * n ^ 2 + 3002 * n + 1) * (n - k * s) ≤ (15 * n ^ 2 + 3002 * n + 1) * k :=
    Nat.mul_le_mul_left _ hrem
  calc optimalLength B ≤ _ := hres
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm') _)
      (Nat.mul_le_mul_left 2 hpb)

end SlidingPuzzle.Port
