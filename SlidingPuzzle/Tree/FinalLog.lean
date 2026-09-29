import SlidingPuzzle.Tree.FineLog
import SlidingPuzzle.Tree.Final

/-! # The tree bound for a lane system, against the logarithmic slack

`optimalLength_le_lanes` asks for `256·depth ≤ q` and `2λ ≤ q`, which ties the lane
width to the depth. Here the hypotheses are only what the run needs: `8k²q ≤ n`,
`16k²λ ≤ n` (the lane width and the residence windows), `4·depth ≤ λ` (the reserve
fits), `λ ≥ 64` and `k ≥ 64`. The cost is `(48·depth + 142) k² s³`. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {n k s q : ℕ} (L : LaneSys k q)

/-- The certified tree bound is at most `(48·depth + 142) k² s³`. -/
theorem treeBound_le_log [NeZero n] (td : TDims n k s q) (hk : 64 ≤ k)
    (hl : 64 ≤ GroupedOrder.lamN n) (hkq : 8 * k * q ≤ s)
    (hlam : 16 * k * GroupedOrder.lamN n ≤ s) :
    treeBound L n s ≤ (48 * L.depth + 142) * (k ^ 2 * s ^ 3) := by
  have hn := td.mul
  subst n
  apply polynomial_budget_log k q s L.depth _ _ _ _ hk hl hkq hlam
  · exact laneCells_bound L
  · exact total_need_le L _
  · exact total_resv_le L td

theorem lamN_mono {a b : ℕ} (h : a ≤ b) : GroupedOrder.lamN a ≤ GroupedOrder.lamN b := by
  unfold GroupedOrder.lamN
  have := Nat.log_mono_right (b := 2) h
  omega

theorem lamN_ge_of_pow {m e : ℕ} (h : 2 ^ e ≤ m) : 3 * (e + 1) ≤ GroupedOrder.lamN m := by
  unfold GroupedOrder.lamN
  have : e ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) h
  omega

open SlidingPuzzle in
/-- The tree bound for any lane system of depth `h` on `k ≥ 64` blocks with `q` offsets,
once `8 k² q ≤ n`, `16 k² λ ≤ n`, `4h ≤ λ` and `λ ≥ 64`. -/
theorem optimalLength_le_lanes_log {n k q h : ℕ} [NeZero n] (L : LaneSys k q)
    (hd : L.depth = h) (hke : Even k) (hqe : Even q) (hq2 : 2 ≤ q) (hqk : q ≤ k)
    (hk : 64 ≤ k) (hl : 64 ≤ GroupedOrder.lamN n) (hh4 : 4 * h ≤ GroupedOrder.lamN n)
    (hlo : 8 * k * q * k ≤ n) (hlo2 : 16 * k * GroupedOrder.lamN n * k ≤ n)
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * k) +
      2 * ((48 * h + 142) * k ^ 2 * (n / k) ^ 3) := by
  set s := n / k with hs
  have hk0 : 0 < k := by omega
  have hsq : 8 * k * q ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le hk0]; exact hlo
  have hsl : 16 * k * GroupedOrder.lamN n ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le hk0]; exact hlo2
  have hn' : k * s ≤ n := Nat.mul_div_le n k
  have hks : 1024 * k ≤ s := by
    have : 1024 * k ≤ 16 * k * GroupedOrder.lamN n := by
      have := Nat.mul_le_mul_left (16 * k) hl
      calc 1024 * k = 16 * k * 64 := by ring
        _ ≤ _ := this
    omega
  have hdim : TDims (k * s) k s q := by
    refine ⟨⟨by omega, hke, by omega, rfl, by omega⟩, hq2, hqe, hqk⟩
  -- `λ` of the reduced board `k s`: at most `λ n`, and still at least `64`
  have hlam_le : GroupedOrder.lamN (k * s) ≤ GroupedOrder.lamN n := lamN_mono hn'
  have hks22 : 2 ^ 21 ≤ k * s := by
    have h1 : 64 * (1024 * 64) ≤ k * s := Nat.mul_le_mul hk (le_trans (by omega) hks)
    calc 2 ^ 21 ≤ 64 * (1024 * 64) := by norm_num
      _ ≤ _ := h1
  have hl' : 64 ≤ GroupedOrder.lamN (k * s) :=
    le_trans (by norm_num) (lamN_ge_of_pow hks22)
  have h16 : 16 * k * GroupedOrder.lamN (k * s) ≤ s :=
    le_trans (Nat.mul_le_mul_left _ hlam_le) hsl
  have h64 : 64 * L.depth * k ≤ s := by
    rw [hd]
    have : 64 * h * k ≤ 16 * k * GroupedOrder.lamN n := by
      have := Nat.mul_le_mul_left (16 * k) hh4
      calc 64 * h * k = 16 * k * (4 * h) := by ring
        _ ≤ _ := this
    omega
  have hs100 : 100 ≤ s := by omega
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
  have htb := treeBound_le_log L hdim hk hl' hsq h16
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
      2 * ((48 * h + 142) * (k ^ 2 * s ^ 3)) :=
    hres'.trans (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm') _)
      (Nat.mul_le_mul_left 2 htb))
  calc optimalLength B ≤ _ := hfinal
    _ = _ := by rw [hs]; ring

end SlidingPuzzle.Tree
