import SlidingPuzzle.Tree.AsympAccounting
import SlidingPuzzle.Tree.AsympBound
import SlidingPuzzle.Tree.Feasibility
import SlidingPuzzle.Tree.GridChoice
import SlidingPuzzle.Tree.ReserveAccounting

/-! # The exponent `5/2 + ε`

Grid choice, feasibility of every hypothesis of the tree algorithm and the final
boardwise bound. -/
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
/-- The tree bound on a board of side `n` for a grid of `k = b^h` squares per side,
`b` even and large, `b^(2h+2) ≤ n ≤ (2b)^(2h+2)`. -/
theorem optimalLength_le_grid {n b h : ℕ} [NeZero n] (hh : 1 ≤ h) (hbe : Even b)
    (hb : 160 * (2 * h + 3) ≤ b) (hlo : b ^ (2 * h + 2) ≤ n) (hhi : n ≤ (2 * b) ^ (2 * h + 2))
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * b ^ h) +
      2 * (100000 * (h + 1) * (b ^ h) ^ 2 * (n / b ^ h) ^ 3) := by
  have hb2 : 2 ≤ b := by omega
  have hh0 : 0 < h := hh
  set k := b ^ h with hk
  set s := n / k with hs
  set q := h * b with hq
  let L := Hier.sys b h hb2 hh0
  have hk1 : 1 ≤ k := Nat.one_le_pow _ _ (by omega)
  have hsk : b ^ (h + 2) ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le (by omega), ← pow_add]
    exact (Nat.pow_le_pow_right (by omega) (by omega)).trans hlo
  have hsk' : b ^ 2 * k ≤ s := by
    have : b ^ (h + 2) = b ^ 2 * k := by rw [hk]; ring
    omega
  have hb2b : 26000 ≤ b * b := by nlinarith
  have hsb : b * b * k ≤ s := by nlinarith
  have hk2 : 2 ≤ k := by
    calc 2 ≤ b := hb2
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ h := Nat.pow_le_pow_right (by omega) hh
  have hq_le : q ≤ k := by
    have := offsets_le_grid hb2 h hh0
    simpa [hq, hk] using this
  have h8 : 8 * k * q ≤ s := by
    have : 8 * q ≤ b * b := by
      have : 8 * h ≤ b := by omega
      calc 8 * q = (8 * h) * b := by rw [hq]; ring
        _ ≤ b * b := Nat.mul_le_mul_right _ this
    nlinarith
  have hn' : k * s ≤ n := Nat.mul_div_le n k
  have hdim : TDims (k * s) k s q := by
    refine ⟨⟨hk2, ?_, ?_, rfl, ?_⟩, ?_, ?_, hq_le⟩
    · exact hbe.pow_of_ne_zero (by omega)
    · nlinarith
    · nlinarith
    · have : 2 ≤ h * b := by nlinarith
      exact this
    · obtain ⟨c, hc⟩ := hbe
      exact ⟨h * c, by rw [hq, hc]; ring⟩
  have hlam : GroupedOrder.lamN (k * s) ≤ 10 * ((2 * h + 2) + 1) * b :=
    log_slack_le (by omega) (hn'.trans hhi)
  have h16 : 16 * k * GroupedOrder.lamN (k * s) ≤ s := by
    have : 16 * GroupedOrder.lamN (k * s) ≤ b * b := by
      have : 160 * (2 * h + 3) * b ≤ b * b := Nat.mul_le_mul_right _ hb
      nlinarith
    nlinarith
  have hdepth : L.depth = h := rfl
  have h64 : 64 * L.depth * k ≤ s := by
    rw [hdepth]
    have : 64 * h ≤ b * b := by nlinarith
    nlinarith
  have hs100 : 100 ≤ s := by
    have : 100 * k ≤ b * b * k := Nat.mul_le_mul_right _ (by omega)
    omega
  have : NeZero (k * s) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hfit := hfit_of_grid L hdim hs100 h8 h16 h64
  have hev := event_bounds hdim h8
  have hcap : 76 * k * GroupedOrder.lamN (k * s) ≤ 5 * s :=
    calc 76 * k * GroupedOrder.lamN (k * s) ≤ 80 * k * GroupedOrder.lamN (k * s) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 5 * (16 * k * GroupedOrder.lamN (k * s)) := by ring
      _ ≤ 5 * s := by omega
  have hres := optimalLength_le_tree_residual (n := n) (k := k) (q := q)
    (la := GroupedOrder.lamN (k * s)) L hdim hfit hcap hev.1 hev.2 B
  have hkq : k * q ≤ s :=
    calc k * q ≤ 8 * (k * q) := Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 8 * k * q := by ring
      _ ≤ s := h8
  have hkl : k * GroupedOrder.lamN (k * s) ≤ s :=
    calc k * GroupedOrder.lamN (k * s) ≤ 16 * (k * GroupedOrder.lamN (k * s)) :=
          Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 16 * k * GroupedOrder.lamN (k * s) := by ring
      _ ≤ s := h16
  have htb := treeBound_le L hdim hkq hkl
  have hrem : n - k * (n / k) ≤ k := by
    have := Nat.mod_lt n (show 0 < k by omega)
    have := Nat.mod_add_div n k
    omega
  have hL : L.depth + 1 = h + 1 := rfl
  have htb' : treeBound L (k * s) s ≤ 100000 * (h + 1) * (k ^ 2 * s ^ 3) := by
    rw [hL] at htb; exact htb
  have hres' : optimalLength B ≤ manhattan B.val +
      2 * ((15 * n ^ 2 + 3002 * n + 1) * (n - k * s)) + 2 * treeBound L (k * s) s := hres
  have hrem' : n - k * s ≤ k := hrem
  have hm' : (15 * n ^ 2 + 3002 * n + 1) * (n - k * s) ≤ (15 * n ^ 2 + 3002 * n + 1) * k :=
    Nat.mul_le_mul_left _ hrem'
  have : 100000 * (h + 1) * (k ^ 2 * s ^ 3) = 100000 * (h + 1) * k ^ 2 * s ^ 3 := by ring
  omega

open SlidingPuzzle in
/-- Depth `h`: `OPT(B) ≤ M(B) + C n^(5/2 + 1/(2h+2))` for all large `n`. -/
theorem tree_uniform_approximation (h : ℕ) (hh : 1 ≤ h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
          C * (n : ℝ) ^ (5 / 2 + 1 / (2 * (h : ℝ) + 2)) := by
  set B0 := 160 * (2 * h + 3) with hB0
  refine ⟨(6036 + 200000 * ((h : ℝ) + 1)) * 2 ^ h, by positivity,
    (2 * B0) ^ (2 * h + 2), ?_⟩
  intro n hn hn2
  let : NeZero n := ⟨by omega⟩
  intro B
  obtain ⟨b, hbB, hbe, hlo, hhi⟩ := exists_even_branching_grid h hh B0 (by omega) n hn
  have hnat := optimalLength_le_grid (n := n) (b := b) (h := h) hh hbe hbB hlo hhi B
  have hb1 : 1 ≤ b := by omega
  have hK : (0 : ℝ) < (b : ℝ) ^ h := by positivity
  set K : ℝ := (b : ℝ) ^ h with hKdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hcost := grid_tree_cost h hh n b hlo hhi (by omega)
  rw [← hKdef] at hcost
  -- k * s ≤ n
  have hks : K * ((n / b ^ h : ℕ) : ℝ) ≤ n := by
    have : b ^ h * (n / b ^ h) ≤ n := Nat.mul_div_le n _
    rw [hKdef]
    exact_mod_cast this
  have hterm2 : K ^ 2 * ((n / b ^ h : ℕ) : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / K := by
    rw [le_div_iff₀ hK]
    have := pow_le_pow_left₀ (by positivity) hks 3
    nlinarith [this]
  have hK2 : K ^ 2 ≤ n := by
    have h1 : b ^ (2 * h) ≤ b ^ (2 * h + 2) := Nat.pow_le_pow_right hb1 (by omega)
    have h2 : b ^ (2 * h) ≤ n := h1.trans hlo
    have h3 : ((b : ℝ) ^ (2 * h)) ≤ n := by exact_mod_cast h2
    rw [hKdef, ← pow_mul, mul_comm]
    exact h3
  have hterm1 : (15 * (n : ℝ) ^ 2 + 3002 * n + 1) * K ≤ 3018 * ((n : ℝ) ^ 3 / K) := by
    have ha : 15 * (n : ℝ) ^ 2 + 3002 * n + 1 ≤ 3018 * (n : ℝ) ^ 2 := by nlinarith
    have hb' : (n : ℝ) ^ 2 * K ≤ (n : ℝ) ^ 3 / K := by
      rw [le_div_iff₀ hK]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    calc (15 * (n : ℝ) ^ 2 + 3002 * n + 1) * K ≤ (3018 * (n : ℝ) ^ 2) * K :=
          mul_le_mul_of_nonneg_right ha hK.le
      _ = 3018 * ((n : ℝ) ^ 2 * K) := by ring
      _ ≤ 3018 * ((n : ℝ) ^ 3 / K) := by linarith
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * (n : ℝ) ^ 2 + 3002 * n + 1) * K) +
      2 * (100000 * ((h : ℝ) + 1) * (K ^ 2 * ((n / b ^ h : ℕ) : ℝ) ^ 3)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    rw [hKdef]
    linarith [this]
  have hpos : 0 ≤ (n : ℝ) ^ 3 / K := by positivity
  have hh1 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hfinal : 2 * ((15 * (n : ℝ) ^ 2 + 3002 * n + 1) * K) +
      2 * (100000 * ((h : ℝ) + 1) * (K ^ 2 * ((n / b ^ h : ℕ) : ℝ) ^ 3)) ≤
      (6036 + 200000 * ((h : ℝ) + 1)) * ((n : ℝ) ^ 3 / K) := by
    have := mul_le_mul_of_nonneg_left hterm2 (by positivity : (0 : ℝ) ≤ 200000 * ((h : ℝ) + 1))
    nlinarith [hterm1, this]
  calc (optimalLength B : ℝ) ≤ _ := hcast
    _ ≤ (manhattan B.val : ℝ) + (6036 + 200000 * ((h : ℝ) + 1)) * ((n : ℝ) ^ 3 / K) := by
        linarith
    _ ≤ (manhattan B.val : ℝ) + (6036 + 200000 * ((h : ℝ) + 1)) *
          (2 ^ h * (n : ℝ) ^ (5 / 2 + 1 / (2 * (h : ℝ) + 2))) := by
        have := mul_le_mul_of_nonneg_left hcost (by positivity : (0 : ℝ) ≤ 6036 + 200000 * ((h : ℝ) + 1))
        linarith
    _ = _ := by ring

open SlidingPuzzle in
/-- **The exponent `5/2 + ε`**: for every `ε > 0`, `OPT(B) ≤ M(B) + C n^(5/2 + ε)`. -/
theorem tree_exponent {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) + C * (n : ℝ) ^ (5 / 2 + ε) := by
  obtain ⟨h, hh, hle⟩ := exists_depth_for_slack hε
  obtain ⟨C, hC, N, hN⟩ := tree_uniform_approximation h hh
  refine ⟨C, hC, N, fun n hn hn2 B => ?_⟩
  have h1 := hN n hn hn2 B
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have := Real.rpow_le_rpow_of_exponent_le hn1 hle
  have := mul_le_mul_of_nonneg_left this hC
  linarith

end SlidingPuzzle.Tree
