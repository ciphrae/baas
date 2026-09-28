import SlidingPuzzle.Tree.FineAccounting
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
`b` even, `b ≥ 256`, `8h b^(2h+1) ≤ n ≤ (2b)^(2h+2)`. -/
theorem optimalLength_le_grid {n b h : ℕ} [NeZero n] (hh : 1 ≤ h) (hbe : Even b)
    (hb : 256 ≤ b) (hlo : 8 * h * b ^ (2 * h + 1) ≤ n) (hhi : n ≤ (2 * b) ^ (2 * h + 2))
    (B : ReachableBoard n) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * b ^ h) +
      2 * (50 * (h + 3) * (b ^ h) ^ 2 * (n / b ^ h) ^ 3) := by
  have hb2 : 2 ≤ b := by omega
  have hh0 : 0 < h := hh
  set k := b ^ h with hk
  set s := n / k with hs
  set q := h * b with hq
  let L := Hier.sys b h hb2 hh0
  have hbk : b ≤ k := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ h := Nat.pow_le_pow_right (by omega) hh
  have hsb : 8 * h * b * k ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le (by omega)]
    have : 8 * h * b * k * k = 8 * h * b ^ (2 * h + 1) := by rw [hk]; ring
    omega
  have h8 : 8 * k * q ≤ s := by
    have : 8 * k * q = 8 * h * b * k := by rw [hq]; ring
    omega
  have hks : 2048 * h * k ≤ s := by
    have := Nat.mul_le_mul_right (8 * h * k) hb
    have e : 8 * h * b * k = b * (8 * h * k) := by ring
    nlinarith
  have hq_le : q ≤ k := by
    have := offsets_le_grid hb2 h hh0
    simpa [hq, hk] using this
  have hn' : k * s ≤ n := Nat.mul_div_le n k
  have hk2048 : 2048 * k ≤ s := le_trans (Nat.mul_le_mul_right k (by omega)) hks
  have hdim : TDims (k * s) k s q := by
    refine ⟨⟨by omega, ?_, by omega, rfl, by omega⟩, ?_, ?_, hq_le⟩
    · exact hbe.pow_of_ne_zero (by omega)
    · have : 2 ≤ h * b := by nlinarith
      exact this
    · obtain ⟨c, hc⟩ := hbe
      exact ⟨h * c, by rw [hq, hc]; ring⟩
  have hlam2 : 2 * GroupedOrder.lamN (k * s) ≤ h * b :=
    log_slack_fine hh hb (hn'.trans hhi)
  have h16 : 16 * k * GroupedOrder.lamN (k * s) ≤ s := by
    have : 16 * k * GroupedOrder.lamN (k * s) = 8 * k * (2 * GroupedOrder.lamN (k * s)) := by ring
    have h2 := Nat.mul_le_mul_left (8 * k) hlam2
    have e : 8 * k * (h * b) = 8 * h * b * k := by ring
    omega
  have hdepth : L.depth = h := rfl
  have h64 : 64 * L.depth * k ≤ s := by
    rw [hdepth]
    have : 64 * h * k ≤ 2048 * h * k := Nat.mul_le_mul_right k (by omega)
    omega
  have hs100 : 100 ≤ s := by nlinarith
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
  have htb := treeBound_le_fine L hdim (le_trans hb hbk) (by rw [hdepth]; exact hh) h8 h16
    (by rw [hdepth]; exact hks)
  rw [hdepth] at htb
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
    _ = _ := by rw [hs, hk]; ring

theorem exp_eighth_le : Real.exp (1 / 8) ≤ 1.14 := by
  have h1 : Real.exp (1 / 8) ^ 8 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp (1 / 8) ^ 8 ≤ (1.14 : ℝ) ^ 8 := by rw [h1]; norm_num at h2 ⊢; linarith
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 h3

/-- The rounding loss of an even grid: `(b + 2)^h ≤ e^(1/8) b^h` for `b ≥ 16h`. -/
theorem round_loss (h : ℕ) {b : ℝ} (hb : 0 < b) (hbh : 16 * (h : ℝ) ≤ b) :
    (b + 2) ^ h ≤ Real.exp (1 / 8) * b ^ h := by
  have e : b + 2 = b * (2 / b + 1) := by field_simp; ring
  rw [e, mul_pow, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (2 / b + 1) ^ h ≤ Real.exp (2 / b) ^ h :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) h
    _ = Real.exp (h * (2 / b)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (1 / 8) := by
        apply Real.exp_le_exp.2
        rw [show (h : ℝ) * (2 / b) = 2 * h / b by ring, div_le_iff₀ hb]
        linarith

/-- The closing arithmetic of `tree_uniform_approximation_explicit`. -/
theorem final_arith {h O M A T Y S P : ℝ} (hh : 0 ≤ h)
    (hO : O ≤ M + 2 * A + 2 * (50 * (h + 3) * T)) (hA : A ≤ 1 / 128 * Y)
    (hT : 100 * (h + 3) * T ≤ 100 * (h + 3) * Y) (hY : Y ≤ 1.14 * S * P)
    (hS : 0 ≤ S) (hP : 0 ≤ P) :
    O ≤ M + 120 * (h + 3) * S * P := by
  have hSP : 0 ≤ S * P := mul_nonneg hS hP
  have h1 : O ≤ M + (100 * (h + 3) + 1 / 64) * Y := by nlinarith
  have h2 : (100 * (h + 3) + 1 / 64) * Y ≤ (100 * (h + 3) + 1 / 64) * (1.14 * S * P) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  nlinarith

open SlidingPuzzle in
/-- **The explicit tree bound** at depth `h ≥ 1`: for `n ≥ 8h (max(256, 16h) + 2)^(2h+1)`,
`OPT(B) ≤ M(B) + 120 (h+3) √(8h) n^(5/2 + 1/(4h+2))`. -/
theorem tree_uniform_approximation_explicit (h : ℕ) (hh : 1 ≤ h) {n : ℕ} [NeZero n]
    (hn : 8 * h * (max 256 (16 * h) + 2) ^ (2 * h + 1) ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      120 * ((h : ℝ) + 3) * Real.sqrt (8 * h) * (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) := by
  set Bm := max 256 (16 * h) with hBm
  set D := 2 * h + 1 with hD
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set c : ℝ := 8 * h with hc
  have hc0 : 0 < c := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set x : ℝ := ((n : ℝ) / c) ^ (1 / (D : ℝ)) with hx
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hxD : x ^ D = n / c := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show 1 / (D : ℝ) * D = 1 by field_simp, Real.rpow_one]
  have hx0 : 0 ≤ x := by positivity
  have hxB : (Bm : ℝ) + 2 ≤ x := by
    have h1 : c * ((Bm : ℝ) + 2) ^ D ≤ n := by
      rw [hc]; exact_mod_cast hn
    have h2 : ((Bm : ℝ) + 2) ^ D ≤ x ^ D := by
      rw [hxD, le_div_iff₀ hc0, mul_comm]; exact h1
    exact (pow_le_pow_iff_left₀ (by positivity) hx0 (by omega)).1 h2
  set t := ⌊x / 2⌋₊ with ht
  set b := 2 * t with hbdef
  have hbx : (b : ℝ) ≤ x := by
    have := Nat.floor_le (show 0 ≤ x / 2 by positivity)
    rw [hbdef]; push_cast; linarith
  have hxb : x < b + 2 := by
    have := Nat.lt_floor_add_one (x / 2)
    rw [hbdef]; push_cast; linarith
  have hbB : Bm ≤ b := by
    have : (Bm : ℝ) < b + 1 := by linarith
    have : Bm < b + 1 := by exact_mod_cast this
    omega
  have hb256 : 256 ≤ b := le_trans (le_max_left _ _) hbB
  have hb16 : 16 * h ≤ b := le_trans (le_max_right _ _) hbB
  have hbe : Even b := ⟨t, by omega⟩
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hnx : (n : ℝ) = c * x ^ D := by rw [hxD]; field_simp
  have hlo : 8 * h * b ^ D ≤ n := by
    have : c * (b : ℝ) ^ D ≤ n := by
      rw [hnx]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0.le hbx D) hc0.le
    rw [hc] at this; exact_mod_cast this
  have hhi : n ≤ (2 * b) ^ (2 * h + 2) := by
    have h16 : (16 * h : ℝ) ≤ b := by exact_mod_cast hb16
    have h256 : (256 : ℝ) ≤ b := by exact_mod_cast hb256
    have hc2 : c ≤ 2 * (b : ℝ) := by rw [hc]; linarith
    have hxp : x ^ D ≤ (2 * (b : ℝ)) ^ D := pow_le_pow_left₀ hx0 (by linarith) D
    have : (n : ℝ) ≤ (2 * (b : ℝ)) ^ (D + 1) :=
      calc (n : ℝ) = c * x ^ D := hnx
        _ ≤ (2 * (b : ℝ)) * (2 * (b : ℝ)) ^ D :=
          mul_le_mul hc2 hxp (by positivity) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    exact_mod_cast this
  have hnat := optimalLength_le_grid hh hbe hb256 hlo hhi B
  -- real estimates
  set K : ℝ := (b : ℝ) ^ h with hKdef
  have hK : 0 < K := by positivity
  have hks : K * ((n / b ^ h : ℕ) : ℝ) ≤ n := by
    have : b ^ h * (n / b ^ h) ≤ n := Nat.mul_div_le n _
    rw [hKdef]; exact_mod_cast this
  have hterm2 : K ^ 2 * ((n / b ^ h : ℕ) : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / K := by
    rw [le_div_iff₀ hK]
    have := pow_le_pow_left₀ (by positivity) hks 3
    nlinarith [this]
  have hK2 : 2048 * K ^ 2 ≤ n := by
    have h1 : c * (b : ℝ) ^ D ≤ n := by rw [hc]; exact_mod_cast hlo
    have h2 : K ^ 2 * b = (b : ℝ) ^ D := by rw [hKdef, hD, ← pow_mul, ← pow_succ]; ring_nf
    have h3 : (2048 : ℝ) ≤ c * b := by
      have : (256 : ℝ) ≤ b := by exact_mod_cast hb256
      rw [hc]; nlinarith
    nlinarith [sq_nonneg K]
  have hn3003 : (3003 : ℝ) ≤ n := by
    have h256 : (256 : ℝ) ≤ b := by exact_mod_cast hb256
    have : (256 : ℝ) ≤ K := le_trans h256 (le_self_pow₀ (by linarith) (by omega))
    nlinarith
  have hterm1 : (15 * (n : ℝ) ^ 2 + 3002 * n + 1) * K ≤ (1 / 128) * ((n : ℝ) ^ 3 / K) := by
    have ha : 15 * (n : ℝ) ^ 2 + 3002 * n + 1 ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
    have hb' : 2048 * ((n : ℝ) ^ 2 * K) ≤ (n : ℝ) ^ 3 / K := by
      rw [le_div_iff₀ hK]
      nlinarith [mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_right ha hK.le]
  have hcast : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      2 * ((15 * (n : ℝ) ^ 2 + 3002 * n + 1) * K) +
      2 * (50 * ((h : ℝ) + 3) * (K ^ 2 * ((n / b ^ h : ℕ) : ℝ) ^ 3)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    rw [hKdef]
    linarith [this]
  -- `n³/K ≤ e^(1/8) √(8h) n^(5/2 + 1/(4h+2))`
  set α : ℝ := (h : ℝ) / (D : ℝ) with hα
  have hα0 : 0 ≤ α := by positivity
  have hαh : α ≤ 1 / 2 := by
    rw [hα, div_le_iff₀ (by positivity)]; push_cast [hD]; linarith
  have hnα : (n : ℝ) ^ α ≤ c ^ α * (Real.exp (1 / 8) * K) := by
    have e1 : (n : ℝ) ^ α = c ^ α * x ^ h := by
      rw [hnx, Real.mul_rpow hc0.le (by positivity), ← Real.rpow_natCast x D,
        ← Real.rpow_mul hx0, hα, show (D : ℝ) * ((h : ℝ) / D) = h by field_simp, Real.rpow_natCast]
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc x ^ h ≤ ((b : ℝ) + 2) ^ h := pow_le_pow_left₀ hx0 hxb.le h
      _ ≤ Real.exp (1 / 8) * K := round_loss h hb0 (by exact_mod_cast hb16)
  have hcα : c ^ α ≤ Real.sqrt c := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by rw [hc]; linarith) hαh
  have hexp : 3 - α = 5 / 2 + 1 / (4 * (h : ℝ) + 2) := by
    rw [hα, hD]; push_cast; field_simp; ring
  have hsplit : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 - α) * (n : ℝ) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]; congr 1; push_cast; ring
  have hmain : (n : ℝ) ^ 3 / K ≤ 1.14 * Real.sqrt c * (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) := by
    rw [div_le_iff₀ hK, hsplit, ← hexp]
    have hp : 0 ≤ (n : ℝ) ^ (3 - α) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hnα hp
    have h2 : c ^ α * (Real.exp (1 / 8) * K) ≤ Real.sqrt c * (1.14 * K) := by
      apply mul_le_mul hcα _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right exp_eighth_le hK.le
    calc (n : ℝ) ^ (3 - α) * (n : ℝ) ^ α ≤ (n : ℝ) ^ (3 - α) * (c ^ α * (Real.exp (1 / 8) * K)) := h1
      _ ≤ (n : ℝ) ^ (3 - α) * (Real.sqrt c * (1.14 * K)) := mul_le_mul_of_nonneg_left h2 hp
      _ = _ := by ring
  exact final_arith (h := (h : ℝ)) (by positivity) hcast hterm1
    (mul_le_mul_of_nonneg_left hterm2 (by positivity)) hmain (Real.sqrt_nonneg _) (by positivity)

open SlidingPuzzle in
/-- Depth `h`: `OPT(B) ≤ M(B) + C n^(5/2 + 1/(4h+2))` for all large `n`. -/
theorem tree_uniform_approximation (h : ℕ) (hh : 1 ≤ h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n,
        (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
          C * (n : ℝ) ^ (5 / 2 + 1 / (4 * (h : ℝ) + 2)) :=
  ⟨120 * ((h : ℝ) + 3) * Real.sqrt (8 * h), by positivity,
    8 * h * (max 256 (16 * h) + 2) ^ (2 * h + 1), fun n hn hn2 =>
    letI : NeZero n := ⟨by omega⟩
    fun B => tree_uniform_approximation_explicit h hh hn B⟩

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
