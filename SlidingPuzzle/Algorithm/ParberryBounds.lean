import SlidingPuzzle.Algorithm.Parberry.ConstructedPrefix
import SlidingPuzzle.Algorithm.SharedPrefixProjection

/-! Unconditional approximation bounds using the constructed Parberry solver
and protected prefix. These retain their explicit lower-order costs; they do
not invoke the stronger conditional coefficient-five contracts. -/
namespace SlidingPuzzle.Algorithm
open SlidingPuzzle.Partition

/-- The constructed solver reduces the complete finishing path to `447*k¹¹`. -/
theorem exists_parberry_finish_path (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hB : Arranged hk B) :
    ∃ p : Path B (target (k^4)), p.length ≤ 447*k^11 := by
  exact exists_finish_path_of_solver Parberry.cubicSolverBound hk B hB

/-- The improved prefix and solver are both constructed, so no phase hypothesis
remains in this fourth-power bound. -/
theorem exists_fourth_power_solution_parberry (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hB : Reachable B) :
    ∃ p : Path B (target (k^4)), p.inefficientMoves ≤ 1088*k^11 ∧
      p.length ≤ manhattan B+2176*k^11 := by
  exact exists_solution_of_phase_bounds
    (preparationContract_of_prefix_bound Parberry.prefixPathBound) transportContract k hk
    (exists_parberry_finish_path k hk) (by norm_num : 274+447 ≤ 2*361) B hB

/-- Explicit arbitrary-size additive bound from the constructed Parberry
prefix and solver, including the boundary remainders of both. -/
theorem optimalLength_le_parberry {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+7104*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_of_shared_prefix_finish_path Parberry.prefixPathBound
    (fun k hk => by
      letI : NeZero (k^4) := ⟨by positivity⟩
      exact exists_parberry_finish_path k hk)
    (by norm_num : 274+447 ≤ 2*361) hn B
  norm_num at h
  exact h

/-- A legal witness for the improved unconditional inefficiency bound. -/
theorem exists_solution_with_parberry_bound {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 3552*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+7104*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength : (p.length : ℝ) ≤ (manhattan B.val : ℝ)+7104*Real.rpow (n : ℝ) (11/4 : ℝ) := by
    rw [hp]
    exact optimalLength_le_parberry hn B
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ)=(manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- Preserve the layer polynomial during arbitrary-size reduction. The prefix
is charged once to inefficiency, rather than using the uniform constant 616. -/
theorem optimalLength_le_parberry_reduction {n k : ℕ} [NeZero n]
    (B : ReachableBoard n) (hk : 2 ≤ k) (hlo : k^4 ≤ n) :
    optimalLength B ≤ manhattan B.val + 2176*k^11 +
      2*((15*n^2+3002*n+1)*(n-k^4)) := by
  letI : NeZero (k^4) := ⟨by positivity⟩
  have hk4 : 4 ≤ k^4 := by nlinarith [Nat.pow_le_pow_left hk 4]
  obtain ⟨C,p,hp,hC⟩ := Parberry.exists_prefix B.val (n-k^4) (by omega)
  have hd : n-k^4+k^4=n := Nat.sub_add_cancel hlo
  obtain ⟨A,hA⟩ := exists_residual_board (n-k^4) hd C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hreachA : Reachable A :=
    residual_reachable (by omega : 2 ≤ k^4) (n-k^4) hd C hC A hA hreachC
  obtain ⟨q,_,hq⟩ := exists_fourth_power_solution_parberry k hk A hreachA
  have h := optimalLength_le_prefix_residual_solution B (n-k^4) hd C p hC A hA q hq
  omega

/-- The size-reduction prefix has leading inefficiency coefficient sixty.
Its boundary costs have strictly smaller exponents. -/
theorem parberry_reduction_budget {n k : ℕ} (hlo : k^4 ≤ n) (hhi : n < (k+1)^4) :
    ((15*n^2+3002*n+1)*(n-k^4) : ℕ) ≤
      (60*Real.rpow (n : ℝ) (11/4 : ℝ)+
        12008*Real.rpow (n : ℝ) (7/4 : ℝ)+4*Real.rpow (n : ℝ) (3/4 : ℝ) : ℝ) := by
  have hwidth := outer_layer_width_le_rpow hlo hhi
  have hmul := mul_le_mul_of_nonneg_left hwidth
    (by positivity : (0 : ℝ) ≤ 15*(n : ℝ)^2+3002*n+1)
  have h2 : Real.rpow (n : ℝ) (3/4 : ℝ)*(n : ℝ)^2 =
      Real.rpow (n : ℝ) (11/4 : ℝ) := by
    convert (Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 2)).symm using 1 <;>
      norm_num [Real.rpow_natCast]
  have h1 : Real.rpow (n : ℝ) (3/4 : ℝ)*(n : ℝ) =
      Real.rpow (n : ℝ) (7/4 : ℝ) := by
    convert (Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 1)).symm using 1 <;>
      norm_num
  push_cast
  nlinarith [h1,h2]

/-- Retaining lower-order prefix costs reduces the leading additive coefficient
from 7104 to 2296 without changing the fourth-power algorithm. -/
theorem optimalLength_le_parberry_lower_order {n : ℕ} [NeZero n]
    (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+
      2296*Real.rpow (n : ℝ) (11/4 : ℝ)+
      24016*Real.rpow (n : ℝ) (7/4 : ℝ)+8*Real.rpow (n : ℝ) (3/4 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  have hnat := optimalLength_le_parberry_reduction B hk hlo
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+2176*(k : ℝ)^11+
      2*(((15*n^2+3002*n+1)*(n-k^4) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hbudget := parberry_reduction_budget hlo hhi
  have hscale := pow_eleven_le_rpow_of_fourth_power_le hlo
  linarith

/-- An unconditional legal solution with sixty units of leading size-reduction
inefficiency and the explicit lower-order remainder. -/
theorem exists_solution_with_parberry_lower_order {n : ℕ} [NeZero n]
    (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 1148*Real.rpow (n : ℝ) (11/4 : ℝ)+
        12008*Real.rpow (n : ℝ) (7/4 : ℝ)+4*Real.rpow (n : ℝ) (3/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+2296*Real.rpow (n : ℝ) (11/4 : ℝ)+
        24016*Real.rpow (n : ℝ) (7/4 : ℝ)+8*Real.rpow (n : ℝ) (3/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength := optimalLength_le_parberry_lower_order hn B
  rw [← hp] at hlength
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ)=(manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- Absorbing the remainder only at ambient sides at least sixteen also gives
an improved uniform bound, without an asymptotic qualification. -/
theorem optimalLength_le_parberry_uniform {n : ℕ} [NeZero n]
    (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+3798*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  have hnat := optimalLength_le_parberry_reduction B hk hlo
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ)+2176*(k : ℝ)^11+
      2*(((15*n^2+3002*n+1)*(n-k^4) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hpoly : 4*(15*n^2+3002*n+1) ≤ 811*n^2 := by
    have hquad : 16*n ≤ n^2 := by nlinarith
    have hconst : 256 ≤ n^2 := by nlinarith
    nlinarith
  have hmul := Nat.mul_le_mul_right (n-k^4) hpoly
  have hcast : 4*(((15*n^2+3002*n+1)*(n-k^4) : ℕ) : ℝ) ≤
      811*((n-k^4 : ℕ)*(n : ℝ)^2) := by
    exact_mod_cast (show 4*((15*n^2+3002*n+1)*(n-k^4)) ≤
      811*((n-k^4)*n^2) by nlinarith [hmul])
  have hbudget := outer_layer_budget_le_rpow hlo hhi
  have hscale := pow_eleven_le_rpow_of_fourth_power_le hlo
  linarith

/-- Uniform counterpart of the lower-order-aware inefficiency theorem. -/
theorem exists_solution_with_parberry_uniform {n : ℕ} [NeZero n]
    (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 1899*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+3798*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength := optimalLength_le_parberry_uniform hn B
  rw [← hp] at hlength
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ)=(manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

end SlidingPuzzle.Algorithm
