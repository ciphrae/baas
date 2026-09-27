import SlidingPuzzle.Hub.AsympAccounting
import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Parberry.Prefix

/-! # The hub algorithm on a board of arbitrary side: natural-number bounds

For a board of side `n ≥ hubLargeN`, let `L = log₂ n + 1`, choose `m ≥ 1` with
`hubA m³ L ≤ n < hubA (m+1)³ L`, `k = 2m`, `s = ⌊n/k⌋`. The Parberry prefix
solves the outer `n - k*s < k` rows and columns, and `exists_hub_solution`
solves the `k*s` residual board. The result (`optimalLength_le_hub`) is

`OPT ≤ M + 2 hubK (X + Y) + 2 Z` with `X, Y, Z ≤ (hubD³ n⁸ L)^(1/3)`,

namely `X = n² s`, `Y = k² n² L`, and `Z` the prefix cost.
The scaled form uses `2 hubScaledKX X/1000 + 2 hubScaledKY Y/1000 + 2 Z`, with cube scales
`599/299`, `1/4`, and `1/1000`, so each cost retains its own coefficient.

Constants to adjust if the hub modules change theirs:
* `hubScaledKX`, `hubScaledKY` retain fractional costs (`hubBound_le_scaled`);
* `hubLargeKX`, `hubLargeKY` retain older large-grid bounds (`hubBound_le_large`);
* `hubKX`, `hubKY` bound `hubBound` generically (`hubBound_le_sharp`);
  `hubK` gives the coarser common-coefficient form;
* `hubA = 64`, with `m ≥ 598`, ensures the capacity hypothesis `hP1`;
  `hubN` satisfies `hubA * (log₂ n + 1) ≤ n` for `n ≥ hubN`;
* `hubD³ ≥ max hubA (8 * 3018³)`. -/
set_option maxRecDepth 4096

namespace SlidingPuzzle.Hub

open SlidingPuzzle

/-- Coefficients of the local and corridor error terms, kept separate.
The capacity lower bounds keep quadratic and linear remainders small. -/
def hubKX : ℕ := 4042
def hubKY : ℕ := 15888

/-- Large-grid coefficients, using `k ≥ 1000` and the residual logarithm `L ≥ 39`. -/
def hubLargeKX : ℕ := 2893
def hubLargeKY : ℕ := 13351

/-- Common coefficient for the compatibility bound. -/
def hubK : ℕ := hubKY

/-- The cube scale of `k`: `hubA m³ (log₂ n + 1) ≈ n` with `k = 2m`. -/
def hubA : ℕ := 21

/-- The size from which `hubA (log₂ n + 1) ≤ n`. -/
def hubN : ℕ := 4096

/-- Above this side (between `2^27` and `2^28`), grid rounding costs at most `64/63`. -/
def hubLargeN : ℕ := 9 * 2 ^ 24

/-- Each of the three error terms has cube at most `hubD³ n⁸ (log₂ n + 1)`. -/
def hubD : ℕ := 6036

/-- Cube scale of `X = n² s` on the large grid: `(21/8)^(1/3) · 64/63 ≤ hubXNum/hubXDen`. -/
def hubXNum : ℕ := 140136
def hubXDen : ℕ := 100000

/-- Cube scale of `Y = k² n² L`: `(64/21²)^(1/3) ≤ hubYNum/hubYDen`. -/
def hubYNum : ℕ := 525510
def hubYDen : ℕ := 1000000

section
variable {n k s : ℕ}

theorem sqCorridor_le_asymp (k s : ℕ) : sqCorridor k s ≤ 2 * (k * s) := by
  unfold sqCorridor
  have h1 : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2 : (k - 1) * (s - k) ≤ k * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  omega

set_option maxHeartbeats 800000 in
theorem hubBound_le_sharp (hd : HDims n k s) (hs500 : 500 ≤ s) :
    hubBound n k s ≤ hubKX * (n ^ 2 * s) + hubKY * (k ^ 2 * n ^ 2 * (Nat.log 2 n + 1)) := by
  obtain ⟨hk2, -, hroom, hmul⟩ := hd
  have hC := sqCorridor_le_asymp k s
  rw [hmul] at hC
  have hn1000' : 1000 ≤ n := by nlinarith
  have hlog9 : 9 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hT := transportBound_le hk2 (show k ≤ s by omega)
    (show 10 ≤ Nat.log 2 (k * s) + 1 by rw [hmul]; omega)
  have hM := misplacedBound_le hk2 (show k ≤ s by omega)
    (show 10 ≤ Nat.log 2 (k * s) + 1 by rw [hmul]; omega)
  rw [hmul] at hT hM
  have hMcost := Nat.mul_le_mul_left (508 * n) hM
  unfold hubBound hubKX hubKY
  generalize transportBound n k s = T at *
  generalize misplacedBound n k = M at *
  generalize sqCorridor k s = C at *
  have hL : 10 ≤ Nat.log 2 n + 1 := by omega
  generalize Nat.log 2 n + 1 = L at *
  subst hmul
  have hs : 1 ≤ s := by omega
  have hk : 1 ≤ k := by omega
  have hks : 1 ≤ k * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have f1 : k * s ≤ (k * s) ^ 2 * s := by
    calc k * s = k * s * 1 * 1 := by ring
      _ ≤ k * s * (k * s) * s := by gcongr
      _ = (k * s) ^ 2 * s := by ring
  have f3 : (k * s) ^ 2 ≤ (k * s) ^ 2 * s := Nat.le_mul_of_pos_right _ hs
  have f3sharp : 500 * (k * s) ^ 2 ≤ (k * s) ^ 2 * s := by
    have h := Nat.mul_le_mul_left ((k * s) ^ 2) (show 500 ≤ s by omega)
    nlinarith
  have f4 : k ^ 2 * s ^ 3 = (k * s) ^ 2 * s := by ring
  have f5 : k ^ 2 * s ^ 2 = (k * s) ^ 2 := by ring
  have f6 : k ^ 2 * s ≤ (k * s) ^ 2 := by
    calc k ^ 2 * s = k ^ 2 * s * 1 := by ring
      _ ≤ k ^ 2 * s * s := by gcongr
      _ = (k * s) ^ 2 := by ring
  have f7 : k ^ 2 ≤ (k * s) ^ 2 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hs) 2
  have f2 : k * s * (k ^ 2 * C) ≤ 2 * (k ^ 2 * (k * s) ^ 2) := by
    calc k * s * (k ^ 2 * C) ≤ k * s * (k ^ 2 * (2 * (k * s))) := by gcongr
      _ = 2 * (k ^ 2 * (k * s) ^ 2) := by ring
  have f8 : k ^ 2 * (k * s) ≤ k ^ 2 * (k * s) ^ 2 * L := by
    calc k ^ 2 * (k * s) = k ^ 2 * (k * s) * 1 * 1 := by ring
      _ ≤ k ^ 2 * (k * s) * (k * s) * L := by gcongr; omega
      _ = k ^ 2 * (k * s) ^ 2 * L := by ring
  have f9 : 10 * (k ^ 2 * (k * s) ^ 2) ≤ k ^ 2 * (k * s) ^ 2 * L := by
    nlinarith [Nat.mul_le_mul_left (k ^ 2 * (k * s) ^ 2) hL]
  have hn1000 : 1000 ≤ k * s := by nlinarith
  have fs500 : 500 ≤ s := by omega
  have f1sharp : 1000 * (k * s) ≤ (k * s) ^ 2 := by nlinarith
  have f6sharp : 500 * (k ^ 2 * s) ≤ (k * s) ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s) fs500
    nlinarith
  have f7sharp : 250000 * k ^ 2 ≤ (k * s) ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2) (Nat.pow_le_pow_left fs500 2)
    nlinarith
  have f8sharp : 10000 * (k ^ 2 * (k * s)) ≤ k ^ 2 * (k * s) ^ 2 * L := by
    have := Nat.mul_le_mul_left (k ^ 2) (Nat.mul_le_mul f1sharp hL)
    nlinarith
  nlinarith only [hT, hMcost, f1sharp, f3sharp, f4, f5, f6sharp, f7sharp, f2, f8sharp, f9,
    Nat.zero_le ((k * s) ^ 2 * s), Nat.zero_le (k ^ 2 * (k * s) ^ 2 * L)]

set_option maxHeartbeats 800000 in
/-- Sharper accounting for the grid used above `hubLargeN`. -/
theorem hubBound_le_large (hd : HDims n k s) (hs500 : 500 ≤ s)
    (hk1000 : 1000 ≤ k) (hL39 : 39 ≤ Nat.log 2 n + 1) :
    hubBound n k s ≤ hubLargeKX * (n ^ 2 * s) + hubLargeKY * (k ^ 2 * n ^ 2 * (Nat.log 2 n + 1)) := by
  obtain ⟨hk2, -, hroom, hmul⟩ := hd
  have hC := sqCorridor_le_asymp k s
  rw [hmul] at hC
  have hn1000' : 1000 ≤ n := by nlinarith
  have hlog9 : 9 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hT := transportBound_le_large hk1000 (show k ≤ s by omega)
    (show 39 ≤ Nat.log 2 (k * s) + 1 by rw [hmul]; omega)
  have hM := misplacedBound_le_large hk2 (show k ≤ s by omega)
    (show 39 ≤ Nat.log 2 (k * s) + 1 by rw [hmul]; omega)
  rw [hmul] at hT hM
  have hMcost := Nat.mul_le_mul_left (508 * n) hM
  unfold hubBound hubLargeKX hubLargeKY
  generalize transportBound n k s = T at *
  generalize misplacedBound n k = M at *
  generalize sqCorridor k s = C at *
  have hL : 39 ≤ Nat.log 2 n + 1 := by omega
  generalize Nat.log 2 n + 1 = L at *
  subst hmul
  have hs : 1 ≤ s := by omega
  have hk : 1 ≤ k := by omega
  have hks : 1 ≤ k * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have f1 : k * s ≤ (k * s) ^ 2 * s := by
    calc k * s = k * s * 1 * 1 := by ring
      _ ≤ k * s * (k * s) * s := by gcongr
      _ = (k * s) ^ 2 * s := by ring
  have f3 : (k * s) ^ 2 ≤ (k * s) ^ 2 * s := Nat.le_mul_of_pos_right _ hs
  have f3sharp : 500 * (k * s) ^ 2 ≤ (k * s) ^ 2 * s := by
    have h := Nat.mul_le_mul_left ((k * s) ^ 2) (show 500 ≤ s by omega)
    nlinarith
  have f4 : k ^ 2 * s ^ 3 = (k * s) ^ 2 * s := by ring
  have f5 : k ^ 2 * s ^ 2 = (k * s) ^ 2 := by ring
  have f6 : k ^ 2 * s ≤ (k * s) ^ 2 := by
    calc k ^ 2 * s = k ^ 2 * s * 1 := by ring
      _ ≤ k ^ 2 * s * s := by gcongr
      _ = (k * s) ^ 2 := by ring
  have f7 : k ^ 2 ≤ (k * s) ^ 2 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hs) 2
  have f2 : k * s * (k ^ 2 * C) ≤ 2 * (k ^ 2 * (k * s) ^ 2) := by
    calc k * s * (k ^ 2 * C) ≤ k * s * (k ^ 2 * (2 * (k * s))) := by gcongr
      _ = 2 * (k ^ 2 * (k * s) ^ 2) := by ring
  have f8 : k ^ 2 * (k * s) ≤ k ^ 2 * (k * s) ^ 2 * L := by
    calc k ^ 2 * (k * s) = k ^ 2 * (k * s) * 1 * 1 := by ring
      _ ≤ k ^ 2 * (k * s) * (k * s) * L := by gcongr; omega
      _ = k ^ 2 * (k * s) ^ 2 * L := by ring
  have f9 : 39 * (k ^ 2 * (k * s) ^ 2) ≤ k ^ 2 * (k * s) ^ 2 * L := by
    nlinarith [Nat.mul_le_mul_left (k ^ 2 * (k * s) ^ 2) hL]
  have hn1000 : 1000 ≤ k * s := by nlinarith
  have fs500 : 500 ≤ s := by omega
  have f1sharp : 1000 * (k * s) ≤ (k * s) ^ 2 := by nlinarith
  have f6sharp : 500 * (k ^ 2 * s) ≤ (k * s) ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2 * s) fs500
    nlinarith
  have f7sharp : 250000 * k ^ 2 ≤ (k * s) ^ 2 := by
    have := Nat.mul_le_mul_left (k ^ 2) (Nat.pow_le_pow_left fs500 2)
    nlinarith
  have f8sharp : 39000 * (k ^ 2 * (k * s)) ≤ k ^ 2 * (k * s) ^ 2 * L := by
    have := Nat.mul_le_mul_left (k ^ 2) (Nat.mul_le_mul f1sharp hL)
    nlinarith
  nlinarith only [hT, hMcost, f1sharp, f3sharp, f4, f5, f6sharp, f7sharp, f2, f8sharp, f9,
    Nat.zero_le ((k * s) ^ 2 * s), Nat.zero_le (k ^ 2 * (k * s) ^ 2 * L)]

/-- Common-coefficient form of the sharper estimate. -/
theorem hubBound_le (hd : HDims n k s) (hs500 : 500 ≤ s) :
    hubBound n k s ≤ hubK * (n ^ 2 * s + k ^ 2 * n ^ 2 * (Nat.log 2 n + 1)) := by
  have h := hubBound_le_sharp hd hs500
  have hcoeff : hubKX ≤ hubKY := by norm_num [hubKX, hubKY]
  have hmul := Nat.mul_le_mul_right (n ^ 2 * s) hcoeff
  unfold hubK
  nlinarith

/-- `64 (j + 1) ≤ 2^j` for `j ≥ 12`. -/
theorem hubA_mul_succ_le_two_pow {j : ℕ} (hj : 12 ≤ j) : hubA * (j + 1) ≤ 2 ^ j := by
  unfold hubA
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih => rw [pow_succ]; omega

theorem hubA_mul_log_le {n : ℕ} (hn : hubN ≤ n) : hubA * (Nat.log 2 n + 1) ≤ n := by
  unfold hubN at hn
  have hj : 12 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  exact (hubA_mul_succ_le_two_pow hj).trans (Nat.pow_log_le_self 2 (by omega))

/-- The half-width `m` of the hub grid (`k = 2m`). -/
theorem exists_half_width {n L : ℕ} (hL : 1 ≤ L) (hn : hubA * L ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ hubA * m ^ 3 * L ≤ n ∧ n < hubA * (m + 1) ^ 3 * L := by
  classical
  have hA : 1 ≤ hubA := by unfold hubA; norm_num
  let P : ℕ → Prop := fun m => hubA * m ^ 3 * L ≤ n
  have hP1 : P 1 := by simpa [P] using hn
  have hn1 : 1 ≤ n := le_trans (Nat.mul_le_mul hA hL) hn
  refine ⟨Nat.findGreatest P n, Nat.le_findGreatest hn1 hP1,
    Nat.findGreatest_spec hn1 hP1, ?_⟩
  by_contra hcon
  push Not at hcon
  set m := Nat.findGreatest P n
  have hle : m + 1 ≤ n := by
    calc m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      _ = 1 * (m + 1) ^ 3 * 1 := by ring
      _ ≤ hubA * (m + 1) ^ 3 * L := by gcongr
      _ ≤ n := hcon
  have := Nat.le_findGreatest (P := P) hle hcon
  omega

/-- Prefix plus hub on the residual board. -/
theorem optimalLength_le_hub_residual {n k : ℕ} [NeZero n] (B : ReachableBoard n)
    (hd : HDims (k * (n / k)) k (n / k))
    (hP1 : 317 * k * (Nat.log 2 (k * (n / k)) + 1) ≤ n / k) (hsk : n / k ≤ k ^ 3) :
    optimalLength B ≤ manhattan B.val + 2 * ((15 * n ^ 2 + 3002 * n + 1) * (n - k * (n / k))) +
      2 * hubBound (k * (n / k)) k (n / k) := by
  have hmn : k * (n / k) ≤ n := Nat.mul_div_le n k
  have hroom := hd.room
  have hk2 := hd.two_le
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
  obtain ⟨q, hq⟩ := exists_hub_solution hd hP1 hsk A hreachA
  have hlen := q.solution_length
  have hq' : q.length ≤ manhattan A + 2 * hubBound (k * (n / k)) k (n / k) := by omega
  have h := optimalLength_le_prefix_residual_solution B (n - k * (n / k)) hdn C p hC A hA q hq'
  omega

/-- Cube bound for `X = n² s`. -/
theorem cube_X_le {n m L : ℕ} (hm : 1 ≤ m) (hhi : n < hubA * (m + 1) ^ 3 * L) :
    (n ^ 2 * (n / (2 * m))) ^ 3 ≤ hubA * n ^ 8 * L := by
  set s := n / (2 * m)
  have hks : 2 * m * s ≤ n := Nat.mul_div_le n (2 * m)
  have hcube : 8 * m ^ 3 * s ^ 3 ≤ n ^ 3 := by
    calc 8 * m ^ 3 * s ^ 3 = (2 * m * s) ^ 3 := by ring
      _ ≤ n ^ 3 := Nat.pow_le_pow_left hks 3
  have hm1 : (m + 1) ^ 3 ≤ 8 * m ^ 3 := by
    calc (m + 1) ^ 3 ≤ (2 * m) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * m ^ 3 := by ring
  have hn8 : n ≤ hubA * L * (8 * m ^ 3) := by
    calc n ≤ hubA * (m + 1) ^ 3 * L := hhi.le
      _ ≤ hubA * (8 * m ^ 3) * L := by gcongr
      _ = hubA * L * (8 * m ^ 3) := by ring
  -- `s³ n ≤ hubA L n³`, then cancel `n`
  have hsn : s ^ 3 * n ≤ hubA * L * n ^ 2 * n := by
    calc s ^ 3 * n ≤ s ^ 3 * (hubA * L * (8 * m ^ 3)) := Nat.mul_le_mul_left _ hn8
      _ = hubA * L * (8 * m ^ 3 * s ^ 3) := by ring
      _ ≤ hubA * L * n ^ 3 := Nat.mul_le_mul_left _ hcube
      _ = hubA * L * n ^ 2 * n := by ring
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0; simp
  have hs3 : s ^ 3 ≤ hubA * L * n ^ 2 := Nat.le_of_mul_le_mul_right hsn hn0
  calc (n ^ 2 * s) ^ 3 = n ^ 6 * s ^ 3 := by ring
    _ ≤ n ^ 6 * (hubA * L * n ^ 2) := Nat.mul_le_mul_left _ hs3
    _ = hubA * n ^ 8 * L := by ring

/-- The corridor term has cube scale `hubYNum/hubYDen`. -/
theorem cube_scaled_Y_le {n m L : ℕ} (hlo : hubA * m ^ 3 * L ≤ n) :
    (hubYDen * ((2 * m) ^ 2 * n ^ 2 * L)) ^ 3 ≤ hubYNum ^ 3 * n ^ 8 * L := by
  have h2 := Nat.pow_le_pow_left hlo 2
  have hh := Nat.mul_le_mul_left (n ^ 6 * L) h2
  unfold hubA at hh
  unfold hubYNum hubYDen
  nlinarith only [hh, Nat.zero_le (n ^ 8 * L)]

/-- Unscaled form of the corridor cube estimate. -/
theorem cube_Y_le {n m L : ℕ} (hlo : hubA * m ^ 3 * L ≤ n) :
    ((2 * m) ^ 2 * n ^ 2 * L) ^ 3 ≤ 1 ^ 3 * n ^ 8 * L := by
  have h2 := Nat.pow_le_pow_left hlo 2
  have hh := Nat.mul_le_mul_left (n ^ 6 * L) h2
  unfold hubA at hh
  nlinarith only [hh, Nat.zero_le (n ^ 8 * L), Nat.zero_le (m ^ 6 * n ^ 6 * L ^ 3)]

/-- The large-board grid has at least 63 half-columns. -/
theorem half_width_large {n m : ℕ} (hn : hubLargeN ≤ n)
    (hhi : n < hubA * (m + 1) ^ 3 * (Nat.log 2 n + 1)) : 63 ≤ m := by
  unfold hubLargeN at hn
  have hj : 27 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hpow (j : ℕ) (hj : 28 ≤ j) : hubA * 63 ^ 3 * (j + 1) ≤ 2 ^ j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num [hubA]
    | succ j hj ih =>
      rw [pow_succ]
      norm_num [hubA] at ih ⊢
      omega
  by_contra h
  have hm : (m + 1) ^ 3 ≤ 63 ^ 3 := Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.lt_of_not_ge h)) 3
  have := Nat.mul_le_mul_right (Nat.log 2 n + 1) (Nat.mul_le_mul_left hubA hm)
  rcases (show Nat.log 2 n = 27 ∨ 28 ≤ Nat.log 2 n by omega) with h27 | h28
  · rw [h27] at this hhi
    norm_num [hubA] at this hhi
    omega
  · have hle := (hpow _ h28).trans (Nat.pow_log_le_self 2 (by omega))
    omega

/-- Retain the `64/63` rounding ratio instead of the factor two. -/
theorem cube_X_le_large {n m L : ℕ} (hm : 63 ≤ m)
    (hhi : n < hubA * (m + 1) ^ 3 * L) :
    (hubXDen * (n ^ 2 * (n / (2 * m)))) ^ 3 ≤ hubXNum ^ 3 * n ^ 8 * L := by
  set s := n / (2 * m)
  have hks : 2 * m * s ≤ n := Nat.mul_div_le n (2 * m)
  have hc : 8 * m ^ 3 * s ^ 3 ≤ n ^ 3 := by
    simpa only [mul_pow, show (2 : ℕ) ^ 3 = 8 by norm_num] using Nat.pow_le_pow_left hks 3
  have hm1 := Nat.pow_le_pow_left (show 63 * (m + 1) ≤ 64 * m by omega) 3
  have hh := Nat.mul_le_mul_left (63 ^ 3) hhi.le
  have hh2 := Nat.mul_le_mul_left (hubA * L) hm1
  have hn : 63 ^ 3 * n ≤ hubA * L * 64 ^ 3 * m ^ 3 := by nlinarith only [hh, hh2]
  have hsn := Nat.mul_le_mul_left (8 * s ^ 3) hn
  have hcn := Nat.mul_le_mul_left (hubA * L * 64 ^ 3) hc
  have hcancel : 8 * 63 ^ 3 * s ^ 3 * n ≤ hubA * 64 ^ 3 * L * n ^ 2 * n := by
    nlinarith only [hsn, hcn]
  rcases Nat.eq_zero_or_pos n with hz | hz
  · subst n; simp
  have hs3 := Nat.le_of_mul_le_mul_right hcancel hz
  have hq : hubA * 64 ^ 3 * hubXDen ^ 3 ≤ 8 * 63 ^ 3 * hubXNum ^ 3 := by
    norm_num [hubA, hubXDen, hubXNum]
  have h1 := Nat.mul_le_mul_left (hubXDen ^ 3) hs3
  have h2 := Nat.mul_le_mul_right (L * n ^ 2) hq
  have h3 : hubXDen ^ 3 * s ^ 3 ≤ hubXNum ^ 3 * (L * n ^ 2) := by
    have : 8 * 63 ^ 3 * (hubXDen ^ 3 * s ^ 3) ≤ 8 * 63 ^ 3 * (hubXNum ^ 3 * (L * n ^ 2)) := by
      nlinarith only [h1, h2]
    exact Nat.le_of_mul_le_mul_left this (by norm_num)
  have := Nat.mul_le_mul_left (n ^ 6) h3
  calc (hubXDen * (n ^ 2 * s)) ^ 3 = n ^ 6 * (hubXDen ^ 3 * s ^ 3) := by ring
    _ ≤ n ^ 6 * (hubXNum ^ 3 * (L * n ^ 2)) := this
    _ = hubXNum ^ 3 * n ^ 8 * L := by ring

/-- Past `2^27`, `8·2^j` exceeds `21 (3(j+1)+1)³ (j+1)`. -/
theorem grid_pow_gt {j : ℕ} (hj : 27 ≤ j) :
    21 * (3 * (j + 1) + 1) ^ 3 * (j + 1) < 8 * 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have hstep : 21 * (3 * (j + 1 + 1) + 1) ^ 3 * (j + 1 + 1) ≤
        2 * (21 * (3 * (j + 1) + 1) ^ 3 * (j + 1)) := by
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 27 := ⟨j - 27, by omega⟩
      ring_nf
      nlinarith [Nat.zero_le t, Nat.zero_le (t ^ 2), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 4)]
    rw [pow_succ 2 j]
    omega

/-- On the large grid the logarithm is small against the half-width. -/
theorem log_le_half_width {n m : ℕ} (hn : hubLargeN ≤ n)
    (hhi : n < hubA * (m + 1) ^ 3 * (Nat.log 2 n + 1)) :
    3 * (Nat.log 2 n + 1) ≤ 2 * m := by
  unfold hubLargeN at hn
  have hj : 27 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hpow := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hg := grid_pow_gt hj
  by_contra h
  have h3 : 2 * (m + 1) ≤ 3 * (Nat.log 2 n + 1) + 1 := by omega
  have hc := Nat.pow_le_pow_left h3 3
  have hh := Nat.mul_le_mul_left (21 * (Nat.log 2 n + 1)) hc
  unfold hubA at hhi
  nlinarith only [hh, hhi, hpow, hg]

/-- The grid satisfies `s ≤ k³`. -/
theorem div_le_cube_large {n m : ℕ} (hn : hubLargeN ≤ n) (hm : 63 ≤ m)
    (hhi : n < hubA * (m + 1) ^ 3 * (Nat.log 2 n + 1)) :
    n / (2 * m) ≤ (2 * m) ^ 3 := by
  have hL := log_le_half_width hn hhi
  have hm1 := Nat.pow_le_pow_left (show 63 * (m + 1) ≤ 64 * m by omega) 3
  have h1 := Nat.mul_le_mul_left (21 * (m + 1) ^ 3) hL
  have h2 := Nat.mul_le_mul_left (42 * m) hm1
  have hn4 : n ≤ 2 * m * (2 * m) ^ 3 := by
    unfold hubA at hhi
    nlinarith only [hhi, h1, h2, Nat.zero_le (m ^ 4)]
  exact (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr (by nlinarith only [hn4])

/-- Cube bound for the prefix cost `Z`. -/
theorem cube_Z_le {n m L : ℕ} (hm : 1 ≤ m) (hL : 1 ≤ L) (hlo : hubA * m ^ 3 * L ≤ n) :
    ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))) ^ 3 ≤
      8 * 3018 ^ 3 * n ^ 8 * L := by
  have hA : 1 ≤ hubA := by unfold hubA; norm_num
  have hm3 : m ^ 3 ≤ n := by
    calc m ^ 3 = 1 * m ^ 3 * 1 := by ring
      _ ≤ hubA * m ^ 3 * L := by gcongr
      _ ≤ n := hlo
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hm3
  have hd : n - 2 * m * (n / (2 * m)) ≤ 2 * m := by
    have h := Nat.mod_add_div n (2 * m)
    have := Nat.mod_lt n (by omega : 0 < 2 * m)
    omega
  have hpoly : 15 * n ^ 2 + 3002 * n + 1 ≤ 3018 * n ^ 2 := by nlinarith
  have hZ : (15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m))) ≤ 3018 * n ^ 2 * (2 * m) :=
    Nat.mul_le_mul hpoly hd
  calc ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))) ^ 3
      ≤ (3018 * n ^ 2 * (2 * m)) ^ 3 := Nat.pow_le_pow_left hZ 3
    _ = 8 * 3018 ^ 3 * n ^ 6 * m ^ 3 := by ring
    _ ≤ 8 * 3018 ^ 3 * n ^ 6 * n := Nat.mul_le_mul_left _ hm3
    _ = 8 * 3018 ^ 3 * n ^ 7 * 1 := by ring
    _ ≤ 8 * 3018 ^ 3 * n ^ 7 * (n * L) := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr
        (by positivity))
    _ = 8 * 3018 ^ 3 * n ^ 8 * L := by ring

/-- Above the large-board threshold the prefix is lower order: even a
thousand times its cost has cube at most `n⁸ L`. -/
theorem cube_Z_le_large {n m L : ℕ} (hn : hubLargeN ≤ n) (hm : 1 ≤ m)
    (hL : 28 ≤ L) (hlo : hubA * m ^ 3 * L ≤ n) :
    (400 * ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m))))) ^ 3 ≤
      1 ^ 3 * n ^ 8 * L := by
  have hd : n - 2 * m * (n / (2 * m)) ≤ 2 * m := by
    have := Nat.mod_add_div n (2 * m)
    have := Nat.mod_lt n (by omega : 0 < 2 * m)
    omega
  have hpoly : 15 * n ^ 2 + 3002 * n + 1 ≤ 16 * n ^ 2 := by
    unfold hubLargeN at hn
    nlinarith
  have hZ := Nat.pow_le_pow_left (Nat.mul_le_mul_left 400 (Nat.mul_le_mul hpoly hd)) 3
  have hm3 : 588 * m ^ 3 ≤ n := by
    have := Nat.mul_le_mul_left (21 * m ^ 3) hL
    unfold hubA at hlo
    nlinarith
  have hmul := Nat.mul_le_mul_left (3566585035 * n ^ 6) hm3
  have hscale : 3566585035 * n ^ 7 ≤ n ^ 8 * L := by
    have hnL : 3566585035 ≤ n * L := by
      unfold hubLargeN at hn
      nlinarith
    calc 3566585035 * n ^ 7 ≤ (n * L) * n ^ 7 := Nat.mul_le_mul_right _ hnL
      _ = n ^ 8 * L := by ring
  calc _ ≤ (400 * (16 * n ^ 2 * (2 * m))) ^ 3 := hZ
    _ = 2097152000000 * (n ^ 6 * m ^ 3) := by ring
    _ ≤ 3566585035 * n ^ 6 * (588 * m ^ 3) := by
        have : 0 ≤ n ^ 6 * m ^ 3 := Nat.zero_le _
        ring_nf; omega
    _ ≤ 3566585035 * n ^ 6 * n := hmul
    _ = 3566585035 * n ^ 7 := by ring
    _ ≤ _ := by simpa using hscale

/-- The whole algorithm on a board of side `n ≥ hubLargeN`, in natural numbers. -/
theorem optimalLength_le_hub_scaled {n : ℕ} [NeZero n] (hn : hubLargeN ≤ n) (B : ReachableBoard n) :
    ∃ X Y Z : ℕ, (hubXDen * X) ^ 3 ≤ hubXNum ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      (hubYDen * Y) ^ 3 ≤ hubYNum ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      (400 * Z) ^ 3 ≤ 1 ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      1000 * optimalLength B ≤ 1000 * manhattan B.val +
        2 * hubScaledKX * X + 2 * hubScaledKY * Y + 2000 * Z := by
  set L := Nat.log 2 n + 1 with hLdef
  have hL : 1 ≤ L := by omega
  obtain ⟨m, hm, hlo, hhi⟩ := exists_half_width hL (hubA_mul_log_le (show hubN ≤ n by unfold hubN hubLargeN at *; omega))
  have hm63 : 63 ≤ m := half_width_large hn hhi
  have hsk : n / (2 * m) ≤ (2 * m) ^ 3 := div_le_cube_large hn hm63 hhi
  set k := 2 * m with hkdef
  set s := n / k with hsdef
  have hA : hubA = 21 := rfl
  have hm2L : 100 * (m ^ 2 * L) ≤ n := by
    have hh := Nat.mul_le_mul_left (m ^ 2 * L) (show 100 ≤ 21*m by omega)
    unfold hubA at hlo
    nlinarith only [hh, hlo]
  have hmcap : 1268 * (m ^ 2 * L) ≤ n := by
    have hh := Nat.mul_le_mul_left (m ^ 2 * L) (show 1268 ≤ 21*m by omega)
    unfold hubA at hlo
    nlinarith only [hh, hlo]
  have hkpos : 0 < k := by omega
  have hroom : 4 * k + 4 ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    have : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) _
    have : m ^ 2 ≤ m ^ 2 * L := Nat.le_mul_of_pos_right _ hL
    rw [hkdef]
    nlinarith
  have hmn : k * s ≤ n := Nat.mul_div_le n k
  have hd : HDims (k * s) k s := ⟨by omega, ⟨m, by omega⟩, hroom, rfl⟩
  have hlog : Nat.log 2 (k * s) ≤ Nat.log 2 n := Nat.log_mono_right hmn
  have hP1 : 317 * k * (Nat.log 2 (k * s) + 1) ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    calc 317 * k * (Nat.log 2 (k * s) + 1) * k ≤ 317 * k * L * k := by gcongr; omega
      _ = 1268 * (m ^ 2 * L) := by rw [hkdef]; ring
      _ ≤ n := hmcap
  have hres := optimalLength_le_hub_residual B hd hP1 hsk
  simp only [← hsdef] at hres
  have hreslarge : 2 ^ 26 ≤ k * s := by
    have hmod := Nat.mod_lt n hkpos
    have heq := Nat.mod_add_div n k
    change n % k + k * s = n at heq
    have hks : k ≤ k * s := Nat.le_mul_of_pos_right _ (by omega)
    unfold hubLargeN at hn
    omega
  have hL37 : 27 ≤ Nat.log 2 (k * s) + 1 := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hreslarge
    omega
  have hbound := hubBound_le_scaled (show 126 ≤ k by omega) hL37 hP1
  -- monotonicity from `k*s` to `n`
  have hX : (k * s) ^ 2 * s ≤ n ^ 2 * s := by gcongr
  have hY : k ^ 2 * (k * s) ^ 2 * (Nat.log 2 (k * s) + 1) ≤ k ^ 2 * n ^ 2 * L := by
    gcongr
    omega
  refine ⟨n ^ 2 * s, k ^ 2 * n ^ 2 * L,
    (15 * n ^ 2 + 3002 * n + 1) * (n - k * s), ?_, ?_, ?_, ?_⟩
  · exact cube_X_le_large hm63 hhi
  · exact cube_scaled_Y_le hlo
  · have hL2 : 28 ≤ L := by
      have : 27 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by unfold hubLargeN at hn; omega)
      omega
    exact cube_Z_le_large hn hm hL2 hlo
  · have hx := Nat.mul_le_mul_left hubScaledKX hX
    have hy := Nat.mul_le_mul_left hubScaledKY hY
    nlinarith

/-- The previous integral large-grid coefficients remain valid. -/
theorem optimalLength_le_hub_sharp {n : ℕ} [NeZero n] (hn : hubLargeN ≤ n) (B : ReachableBoard n) :
    ∃ X Y Z : ℕ, (hubXDen * X) ^ 3 ≤ hubXNum ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      (hubYDen * Y) ^ 3 ≤ hubYNum ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      (400 * Z) ^ 3 ≤ 1 ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      optimalLength B ≤ manhattan B.val + 2 * hubLargeKX * X + 2 * hubLargeKY * Y + 2 * Z := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hopt⟩ := optimalLength_le_hub_scaled hn B
  have hx := Nat.mul_le_mul_right X
    (show hubScaledKX ≤ 1000 * hubLargeKX by norm_num [hubScaledKX, hubLargeKX])
  have hy := Nat.mul_le_mul_right Y
    (show hubScaledKY ≤ 1000 * hubLargeKY by norm_num [hubScaledKY, hubLargeKY])
  refine ⟨X, Y, Z, hX, hY, hZ, ?_⟩
  nlinarith

/-- Compatibility form with a common cube bound for all three terms. -/
theorem optimalLength_le_hub {n : ℕ} [NeZero n] (hn : hubLargeN ≤ n) (B : ReachableBoard n) :
    ∃ X Y Z : ℕ, X ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Y ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Z ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      optimalLength B ≤ manhattan B.val + 2 * hubK * (X + Y) + 2 * Z := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hopt⟩ := optimalLength_le_hub_sharp hn B
  have hscale {W q p : ℕ} (hq : 0 < q) (hp : p ≤ q * hubD)
      (h : (q * W) ^ 3 ≤ p ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) :
      W ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) := by
    have hp3 := Nat.mul_le_mul_right (n ^ 8 * (Nat.log 2 n + 1)) (Nat.pow_le_pow_left hp 3)
    have : q ^ 3 * W ^ 3 ≤ q ^ 3 * (hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) := by
      calc q ^ 3 * W ^ 3 = (q * W) ^ 3 := by ring
        _ ≤ p ^ 3 * n ^ 8 * (Nat.log 2 n + 1) := h
        _ ≤ (q * hubD) ^ 3 * (n ^ 8 * (Nat.log 2 n + 1)) := by rw [mul_assoc]; exact hp3
        _ = q ^ 3 * (hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1)) := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have hXsmall := hscale (by norm_num [hubXDen]) (by norm_num [hubXDen, hubXNum, hubD]) hX
  have hYsmall := hscale (by norm_num [hubYDen]) (by norm_num [hubYDen, hubYNum, hubD]) hY
  have hZsmall := hscale (q := 400) (p := 1) (by norm_num) (by norm_num [hubD]) hZ
  refine ⟨X, Y, Z, hXsmall, hYsmall, hZsmall, ?_⟩
  · have hcoeff : hubLargeKX ≤ hubKY := by norm_num [hubLargeKX, hubKY]
    have hcoeffY : hubLargeKY ≤ hubKY := by norm_num [hubLargeKY, hubKY]
    have hmul := Nat.mul_le_mul_right X hcoeff
    have hmulY := Nat.mul_le_mul_right Y hcoeffY
    unfold hubK
    nlinarith

end

end SlidingPuzzle.Hub
