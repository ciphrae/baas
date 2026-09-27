import SlidingPuzzle.Hub.Transport
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
The sharper form uses `2 hubKX X + 2 hubKY Y + 2 Z`, with cube scales
`599/299`, `1/4`, and `1`, so each cost retains its own coefficient.

Constants to adjust if the hub modules change theirs:
* `hubKX`, `hubKY` bound `hubBound` (`hubBound_le_sharp`);
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
def hubKY : ℕ := 16063

/-- Common coefficient for the compatibility bound. -/
def hubK : ℕ := hubKY

/-- The cube scale of `k`: `hubA m³ (log₂ n + 1) ≈ n` with `k = 2m`. -/
def hubA : ℕ := 64

/-- The size from which `hubA (log₂ n + 1) ≤ n`. -/
def hubN : ℕ := 4096

/-- Above this side, grid rounding costs at most `599/598`. -/
def hubLargeN : ℕ := 2 ^ 39

/-- Each of the three error terms has cube at most `hubD³ n⁸ (log₂ n + 1)`. -/
def hubD : ℕ := 6036

section
variable {n k s : ℕ}

theorem sqCorridor_le_asymp (k s : ℕ) : sqCorridor k s ≤ 2 * (k * s) := by
  unfold sqCorridor
  have h1 : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2 : (k - 1) * (s - k) ≤ k * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  omega

theorem hubBound_le_sharp (hd : HDims n k s) (hs500 : 500 ≤ s) :
    hubBound n k s ≤ hubKX * (n ^ 2 * s) + hubKY * (k ^ 2 * n ^ 2 * (Nat.log 2 n + 1)) := by
  obtain ⟨hk2, -, hroom, hmul⟩ := hd
  have hC := sqCorridor_le_asymp k s
  rw [hmul] at hC
  have hn1000' : 1000 ≤ n := by nlinarith
  have hlog9 : 9 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  unfold hubBound transportBound misplacedBound hubKX hubKY
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
  nlinarith only [f1sharp, f3sharp, f4, f5, f6sharp, f7sharp, f2, f8sharp, f9,
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
    (hP1 : 25 * k * (Nat.log 2 (k * (n / k)) + 1) ≤ n / k) :
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
  obtain ⟨q, hq⟩ := exists_hub_solution hd hP1 A hreachA
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

/-- The denser grid has exact corridor scale `1/4`. -/
theorem cube_scaled_Y_le {n m L : ℕ} (hlo : hubA * m ^ 3 * L ≤ n) :
    (4 * ((2 * m) ^ 2 * n ^ 2 * L)) ^ 3 ≤ 1 ^ 3 * n ^ 8 * L := by
  have h2 := Nat.pow_le_pow_left hlo 2
  have hh := Nat.mul_le_mul_left (n ^ 6 * L) h2
  unfold hubA at hh
  nlinarith only [hh]

/-- Unscaled form of the corridor cube estimate. -/
theorem cube_Y_le {n m L : ℕ} (hlo : hubA * m ^ 3 * L ≤ n) :
    ((2 * m) ^ 2 * n ^ 2 * L) ^ 3 ≤ 1 ^ 3 * n ^ 8 * L := by
  have h := cube_scaled_Y_le hlo
  exact (Nat.pow_le_pow_left (show (2*m)^2*n^2*L ≤ 4*((2*m)^2*n^2*L) by omega) 3).trans h

/-- The large-board grid has at least 598 half-columns. -/
theorem half_width_large {n m : ℕ} (hn : hubLargeN ≤ n)
    (hhi : n < hubA * (m + 1) ^ 3 * (Nat.log 2 n + 1)) : 598 ≤ m := by
  have hj : 39 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow (j : ℕ) (hj : 39 ≤ j) : hubA * 598 ^ 3 * (j + 1) ≤ 2 ^ j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num [hubA]
    | succ j hj ih =>
      rw [pow_succ]
      norm_num [hubA] at ih ⊢
      omega
  have hle := (hpow _ hj).trans (Nat.pow_log_le_self 2 (by unfold hubLargeN at hn; omega))
  by_contra h
  have hm : (m + 1) ^ 3 ≤ 598 ^ 3 := Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.lt_of_not_ge h)) 3
  have := Nat.mul_le_mul_right (Nat.log 2 n + 1) (Nat.mul_le_mul_left hubA hm)
  omega

/-- Retain the `599/598` rounding ratio instead of the factor two. -/
theorem cube_X_le_large {n m L : ℕ} (hm : 598 ≤ m)
    (hhi : n < hubA * (m + 1) ^ 3 * L) :
    (299 * (n ^ 2 * (n / (2 * m)))) ^ 3 ≤ 599 ^ 3 * n ^ 8 * L := by
  set s := n / (2 * m)
  have hks : 2 * m * s ≤ n := Nat.mul_div_le n (2 * m)
  have hc : 8 * m ^ 3 * s ^ 3 ≤ n ^ 3 := by
    simpa only [mul_pow, show (2 : ℕ) ^ 3 = 8 by norm_num] using Nat.pow_le_pow_left hks 3
  have hm1 := Nat.pow_le_pow_left (show 598 * (m + 1) ≤ 599 * m by omega) 3
  have hh := Nat.mul_le_mul_left (598 ^ 3) hhi.le
  have hh2 := Nat.mul_le_mul_left (hubA * L) hm1
  have hn : 598 ^ 3 * n ≤ hubA * L * 599 ^ 3 * m ^ 3 := by nlinarith only [hh, hh2]
  have hsn := Nat.mul_le_mul_left (8 * s ^ 3) hn
  have hcn := Nat.mul_le_mul_left (hubA * L * 599 ^ 3) hc
  have hcancel : 299 ^ 3 * s ^ 3 * n ≤ 599 ^ 3 * L * n ^ 2 * n := by
    unfold hubA at hsn hcn
    nlinarith only [hsn, hcn]
  rcases Nat.eq_zero_or_pos n with hz | hz
  · subst n; simp
  have hs3 := Nat.le_of_mul_le_mul_right hcancel hz
  have := Nat.mul_le_mul_left (n ^ 6) hs3
  nlinarith only [this]

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

/-- Above the explicit threshold the prefix is lower order: its cube fits
inside `n⁸ L`, without the old coarse factor `6036³`. -/
theorem cube_Z_le_large {n m L : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    (hL : 1 ≤ L) (hlo : hubA * m ^ 3 * L ≤ n) :
    ((15 * n ^ 2 + 3002 * n + 1) * (n - 2 * m * (n / (2 * m)))) ^ 3 ≤
      1 ^ 3 * n ^ 8 * L := by
  have hd : n - 2 * m * (n / (2 * m)) ≤ 2 * m := by
    have := Nat.mod_add_div n (2 * m)
    have := Nat.mod_lt n (by omega : 0 < 2 * m)
    omega
  have hpoly : 15 * n ^ 2 + 3002 * n + 1 ≤ 16 * n ^ 2 := by nlinarith
  have hZ := Nat.pow_le_pow_left (Nat.mul_le_mul hpoly hd) 3
  have hm3 : 64 * m ^ 3 ≤ n := by
    have := Nat.mul_le_mul_left (64 * m ^ 3) hL
    unfold hubA at hlo
    nlinarith
  have hmul := Nat.mul_le_mul_left (512 * n ^ 6) hm3
  have hscale : 512 * n ^ 7 ≤ n ^ 8 * L := by
    calc 512 * n ^ 7 ≤ n * n ^ 7 := by gcongr; omega
      _ = n ^ 8 := by ring
      _ ≤ n ^ 8 * L := Nat.le_mul_of_pos_right _ hL
  calc _ ≤ (16 * n ^ 2 * (2 * m)) ^ 3 := hZ
    _ = 32768 * (n ^ 6 * m ^ 3) := by ring
    _ ≤ 32768 * (n ^ 6 * m ^ 3) := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 512 * n ^ 7 := by nlinarith only [hmul]
    _ ≤ _ := by simpa using hscale

/-- The whole algorithm on a board of side `n ≥ hubLargeN`, in natural numbers. -/
theorem optimalLength_le_hub_sharp {n : ℕ} [NeZero n] (hn : hubLargeN ≤ n) (B : ReachableBoard n) :
    ∃ X Y Z : ℕ, (299 * X) ^ 3 ≤ 599 ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      (4 * Y) ^ 3 ≤ 1 ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Z ^ 3 ≤ 1 ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      optimalLength B ≤ manhattan B.val + 2 * hubKX * X + 2 * hubKY * Y + 2 * Z := by
  set L := Nat.log 2 n + 1 with hLdef
  have hL : 1 ≤ L := by omega
  obtain ⟨m, hm, hlo, hhi⟩ := exists_half_width hL (hubA_mul_log_le (show hubN ≤ n by unfold hubN hubLargeN at *; omega))
  have hm598 : 598 ≤ m := half_width_large hn hhi
  set k := 2 * m with hkdef
  set s := n / k with hsdef
  have hA : hubA = 64 := rfl
  have hm2L : 100 * (m ^ 2 * L) ≤ n := by
    have hh := Nat.mul_le_mul_left (m ^ 2 * L) (show 100 ≤ 64*m by omega)
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
  have hP1 : 25 * k * (Nat.log 2 (k * s) + 1) ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    calc 25 * k * (Nat.log 2 (k * s) + 1) * k ≤ 25 * k * L * k := by gcongr; omega
      _ = 100 * (m ^ 2 * L) := by rw [hkdef]; ring
      _ ≤ n := hm2L
  have hres := optimalLength_le_hub_residual B hd hP1
  simp only [← hsdef] at hres
  have hbound := hubBound_le_sharp hd (capacity_lower_bounds hd hP1).2.1
  -- monotonicity from `k*s` to `n`
  have hX : (k * s) ^ 2 * s ≤ n ^ 2 * s := by gcongr
  have hY : k ^ 2 * (k * s) ^ 2 * (Nat.log 2 (k * s) + 1) ≤ k ^ 2 * n ^ 2 * L := by
    gcongr
    omega
  refine ⟨n ^ 2 * s, k ^ 2 * n ^ 2 * L,
    (15 * n ^ 2 + 3002 * n + 1) * (n - k * s), ?_, ?_, ?_, ?_⟩
  · exact cube_X_le_large hm598 hhi
  · exact cube_scaled_Y_le hlo
  · exact cube_Z_le_large (show 4096 ≤ n by unfold hubLargeN at hn; omega) hm hL hlo
  · have hx := Nat.mul_le_mul_left hubKX hX
    have hy := Nat.mul_le_mul_left hubKY hY
    nlinarith

/-- Compatibility form with a common cube bound for all three terms. -/
theorem optimalLength_le_hub {n : ℕ} [NeZero n] (hn : hubLargeN ≤ n) (B : ReachableBoard n) :
    ∃ X Y Z : ℕ, X ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Y ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Z ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      optimalLength B ≤ manhattan B.val + 2 * hubK * (X + Y) + 2 * Z := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hopt⟩ := optimalLength_le_hub_sharp hn B
  have hXsmall : X ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) := by
    have hmono : X ^ 3 ≤ (299 * X) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    exact (hmono.trans hX).trans (by unfold hubD; gcongr; norm_num)
  have hYsmall : Y ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) := by
    have hmono : Y ^ 3 ≤ (4 * Y) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    exact (hmono.trans hY).trans (by unfold hubD; gcongr; norm_num)
  refine ⟨X, Y, Z, hXsmall, hYsmall, hZ.trans ?_, ?_⟩
  · unfold hubD; gcongr; norm_num
  · have hcoeff : hubKX ≤ hubKY := by norm_num [hubKX, hubKY]
    have hmul := Nat.mul_le_mul_right X hcoeff
    unfold hubK
    nlinarith

end

end SlidingPuzzle.Hub
