import SlidingPuzzle.Algorithm.ResidualPotential
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Moves.Prefix
import SlidingPuzzle.Proposition9Reduction

/-! Reduction from a uniform fourth-power algorithm to all sufficiently large dimensions.
The fourth-power algorithm is an explicit input to this reduction. -/
namespace SlidingPuzzle
noncomputable section

/-- The sole algorithmic input to the general-size reduction. -/
def FourthPowerApproximation : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, ∀ hk : 2 ≤ k,
    letI : NeZero (k^4) := ⟨by positivity⟩
    ∀ A : ReachableBoard (k^4),
      optimalLength A ≤ manhattan A.val + K*k^11

/-- Retain the exact outer-layer cost before converting to an asymptotic scale. -/
theorem optimalLength_le_fourth_power_prefix {n : ℕ} [NeZero n]
    (B : ReachableBoard n) (k K : ℕ) (hk : 2 ≤ k)
    (hlo : k^4 ≤ n)
    (hfourth : letI : NeZero (k^4) := ⟨by positivity⟩
      ∀ A : ReachableBoard (k^4), optimalLength A ≤ manhattan A.val + K*k^11) :
    optimalLength B ≤ manhattan B.val + K*k^11 + 2008*((n-k^4)*n^2) := by
  let : NeZero (k^4) := ⟨by positivity⟩
  have hk4 : 4 ≤ k^4 := by nlinarith [Nat.pow_le_pow_left hk 4]
  obtain ⟨C,p,hp,hC⟩ := exists_prefix_path B.val (target n) rfl (n-k^4) (by omega)
  have hd : n-k^4+k^4=n := Nat.sub_add_cancel hlo
  obtain ⟨A,hA⟩ := exists_residual_board (n-k^4) hd C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hm : 2 ≤ k^4 := by omega
  have hreachA : Reachable A := residual_reachable hm (n-k^4) hd C hC A hA hreachC
  let R : ReachableBoard (k^4) := ⟨A,hreachA⟩
  obtain ⟨q,hq⟩ := shortest_witness R
  have hbound : q.length ≤ manhattan A + K*k^11 := by
    rw [hq]
    exact hfourth R
  have h := optimalLength_le_prefix_residual_solution B (n-k^4) hd C p hC A hA q hbound
  nlinarith

/-- A bound for the rounded-down subproblem gives a bound for the original puzzle. -/
theorem optimalLength_le_of_fourth_power_bound {n : ℕ} [NeZero n]
    (B : ReachableBoard n) (k K : ℕ) (hk : 2 ≤ k)
    (hlo : k^4 ≤ n) (hhi : n < (k+1)^4)
    (hfourth : letI : NeZero (k^4) := ⟨by positivity⟩
      ∀ A : ReachableBoard (k^4), optimalLength A ≤ manhattan A.val + K*k^11) :
    optimalLength B ≤ manhattan B.val + (K+7710720)*k^11 := by
  have h := optimalLength_le_fourth_power_prefix B k K hk hlo hfourth
  have hbudget := outer_layer_budget_le (by omega : 1 ≤ k) hhi
  nlinarith

/-- Direct ambient-size accounting adds only `8032` to the fourth-power coefficient. -/
theorem optimalLength_le_of_fourth_power_bound_rpow {n : ℕ} [NeZero n]
    (B : ReachableBoard n) (k K : ℕ) (hk : 2 ≤ k)
    (hlo : k^4 ≤ n) (hhi : n < (k+1)^4)
    (hfourth : letI : NeZero (k^4) := ⟨by positivity⟩
      ∀ A : ReachableBoard (k^4), optimalLength A ≤ manhattan A.val + K*k^11) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      ((K : ℝ)+8032)*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have hbound := optimalLength_le_fourth_power_prefix B k K hk hlo hfourth
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (K : ℝ)*(k : ℝ)^11 + 2008*((n-k^4 : ℕ)*(n : ℝ)^2) := by
    exact_mod_cast hbound
  have hscaled := mul_le_mul_of_nonneg_left
    (pow_eleven_le_rpow_of_fourth_power_le hlo) (Nat.cast_nonneg K)
  have hbudget := outer_layer_budget_le_rpow hlo hhi
  nlinarith

/-- The proved prefix, residual parity, and potential comparison discharge the
general-dimension obligation once the fourth-power algorithm is supplied. -/
theorem uniformApproximation_of_fourthPowerApproximation
    (h : FourthPowerApproximation) : UniformApproximation := by
  obtain ⟨K,hK⟩ := h
  refine ⟨(K : ℝ)+8032, by positivity, 16, ?_⟩
  intro n hn hn2
  let : NeZero n := ⟨by omega⟩
  intro B
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  exact optimalLength_le_of_fourth_power_bound_rpow B k K hk hlo hhi (hK k hk)

open Filter Asymptotics in
/-- Proposition 9 reduced to the fourth-power algorithm, with no remaining
general-size, reachability, potential, or statistical hypotheses. -/
theorem proposition9_of_fourthPowerApproximation (h : FourthPowerApproximation) :
    ((fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ) * (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) ∧
    ((fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) :=
  proposition9_of_uniformApproximation (uniformApproximation_of_fourthPowerApproximation h)

end
end SlidingPuzzle
