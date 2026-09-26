import SlidingPuzzle.Hub.Transport
import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Parberry.Prefix

/-! # The hub algorithm on a board of arbitrary side: natural-number bounds

For a board of side `n ≥ hubN`, let `L = log₂ n + 1`, choose `m ≥ 1` with
`hubA m³ L ≤ n < hubA (m+1)³ L`, `k = 2m`, `s = ⌊n/k⌋`. The Parberry prefix
solves the outer `n - k*s < k` rows and columns, and `exists_hub_solution`
solves the `k*s` residual board. The result (`optimalLength_le_hub`) is

`OPT ≤ M + 2 hubK (X + Y) + 2 Z` with `X, Y, Z ≤ (hubD³ n⁸ L)^(1/3)`,

namely `X = n² s`, `Y = k² n² L`, and `Z` the prefix cost.

Constants to adjust if the hub modules change theirs:
* `hubK` bounds `hubBound` (`hubBound_le`);
* `hubA ≥ 4 * 64` where `64` is the constant of the hypothesis `hP1`,
  and `hubA ≥ 24`; `hubN` must satisfy `hubA * (log₂ n + 1) ≤ n` for `n ≥ hubN`;
* `hubD³ ≥ max hubA (8 * 3018³)`. -/
namespace SlidingPuzzle.Hub

open SlidingPuzzle

/-- `hubBound n k s ≤ hubK (n² s + k² n² (log₂ n + 1))`. -/
def hubK : ℕ := 10 ^ 8

/-- The cube scale of `k`: `hubA m³ (log₂ n + 1) ≈ n` with `k = 2m`. -/
def hubA : ℕ := 256

/-- The size from which `hubA (log₂ n + 1) ≤ n`. -/
def hubN : ℕ := 4096

/-- Each of the three error terms has cube at most `hubD³ n⁸ (log₂ n + 1)`. -/
def hubD : ℕ := 6036

section
variable {n k s : ℕ}

theorem sqCorridor_le_asymp (k s : ℕ) : sqCorridor k s ≤ 2 * (k * s) := by
  unfold sqCorridor
  have h1 : (k - 1) * s ≤ k * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2 : (k - 1) * (s - k) ≤ k * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  omega

theorem hubBound_le (hd : HDims n k s) :
    hubBound n k s ≤ hubK * (n ^ 2 * s + k ^ 2 * n ^ 2 * (Nat.log 2 n + 1)) := by
  obtain ⟨hk2, -, hroom, hmul⟩ := hd
  have hC := sqCorridor_le_asymp k s
  rw [hmul] at hC
  unfold hubBound transportBound misplacedBound hubK
  generalize sqCorridor k s = C at *
  have hL : 1 ≤ Nat.log 2 n + 1 := by omega
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
      _ ≤ k ^ 2 * (k * s) * (k * s) * L := by gcongr
      _ = k ^ 2 * (k * s) ^ 2 * L := by ring
  have f9 : k ^ 2 * (k * s) ^ 2 ≤ k ^ 2 * (k * s) ^ 2 * L := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- `256 (j + 1) ≤ 2^j` for `j ≥ 12`. -/
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
    (hP1 : 64 * k * (Nat.log 2 (k * (n / k)) + 1) ≤ n / k) :
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

/-- Cube bound for `Y = k² n² L`. -/
theorem cube_Y_le {n m L : ℕ} (hlo : hubA * m ^ 3 * L ≤ n) :
    ((2 * m) ^ 2 * n ^ 2 * L) ^ 3 ≤ 64 * n ^ 8 * L := by
  have hA : 1 ≤ hubA := by unfold hubA; norm_num
  have h1 : m ^ 3 * L ≤ n := le_trans (Nat.le_mul_of_pos_left _ hA) (by simpa [mul_assoc] using hlo)
  have h2 : (m ^ 3 * L) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h1 2
  calc ((2 * m) ^ 2 * n ^ 2 * L) ^ 3 = 64 * n ^ 6 * L * (m ^ 3 * L) ^ 2 := by ring
    _ ≤ 64 * n ^ 6 * L * n ^ 2 := Nat.mul_le_mul_left _ h2
    _ = 64 * n ^ 8 * L := by ring

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

/-- The whole algorithm on a board of side `n ≥ hubN`, in natural numbers. -/
theorem optimalLength_le_hub {n : ℕ} [NeZero n] (hn : hubN ≤ n) (B : ReachableBoard n) :
    ∃ X Y Z : ℕ, X ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Y ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      Z ^ 3 ≤ hubD ^ 3 * n ^ 8 * (Nat.log 2 n + 1) ∧
      optimalLength B ≤ manhattan B.val + 2 * hubK * (X + Y) + 2 * Z := by
  set L := Nat.log 2 n + 1 with hLdef
  have hL : 1 ≤ L := by omega
  obtain ⟨m, hm, hlo, hhi⟩ := exists_half_width hL (hubA_mul_log_le hn)
  set k := 2 * m with hkdef
  set s := n / k with hsdef
  have hA : hubA = 256 := rfl
  have hm2L : 256 * (m ^ 2 * L) ≤ n := by
    calc 256 * (m ^ 2 * L) = 256 * (m ^ 2 * 1 * L) := by ring
      _ ≤ 256 * (m ^ 2 * m * L) := by gcongr
      _ = hubA * m ^ 3 * L := by rw [hA]; ring
      _ ≤ n := hlo
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
  have hP1 : 64 * k * (Nat.log 2 (k * s) + 1) ≤ s := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    calc 64 * k * (Nat.log 2 (k * s) + 1) * k ≤ 64 * k * L * k := by gcongr; omega
      _ = 256 * (m ^ 2 * L) := by rw [hkdef]; ring
      _ ≤ n := hm2L
  have hres := optimalLength_le_hub_residual B hd hP1
  simp only [← hsdef] at hres
  have hbound := hubBound_le hd
  -- monotonicity from `k*s` to `n`
  have hX : (k * s) ^ 2 * s ≤ n ^ 2 * s := by gcongr
  have hY : k ^ 2 * (k * s) ^ 2 * (Nat.log 2 (k * s) + 1) ≤ k ^ 2 * n ^ 2 * L := by
    gcongr
    omega
  refine ⟨n ^ 2 * s, k ^ 2 * n ^ 2 * L,
    (15 * n ^ 2 + 3002 * n + 1) * (n - k * s), ?_, ?_, ?_, ?_⟩
  · exact (cube_X_le hm hhi).trans (by unfold hubD; gcongr; rw [hA]; norm_num)
  · exact (cube_Y_le hlo).trans (by unfold hubD; gcongr; norm_num)
  · exact (cube_Z_le hm hL hlo).trans (by unfold hubD; gcongr; norm_num)
  · have h2 : hubBound (k * s) k s ≤ hubK * (n ^ 2 * s + k ^ 2 * n ^ 2 * L) :=
      hbound.trans (Nat.mul_le_mul_left _ (by omega))
    have : 2 * hubBound (k * s) k s ≤ 2 * hubK * (n ^ 2 * s + k ^ 2 * n ^ 2 * L) :=
      calc 2 * hubBound (k * s) k s ≤ 2 * (hubK * (n ^ 2 * s + k ^ 2 * n ^ 2 * L)) :=
            Nat.mul_le_mul_left 2 h2
        _ = 2 * hubK * (n ^ 2 * s + k ^ 2 * n ^ 2 * L) := by ring
    omega

end

end SlidingPuzzle.Hub
