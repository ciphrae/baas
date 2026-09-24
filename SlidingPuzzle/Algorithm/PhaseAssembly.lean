import SlidingPuzzle.Algorithm.Preparation
import SlidingPuzzle.Algorithm.Arrangement
import SlidingPuzzle.Algorithm.Finish
import SlidingPuzzle.Algorithm.Transport

/-! Composition of the four constructed phases. The parameterized wrappers
remain available, while the concrete package has no phase hypotheses. -/
namespace SlidingPuzzle.Algorithm

open SlidingPuzzle.Partition

/-- Arrange and finish form one solving suffix. Its combined all-moves budget
can be halved, even though arrangement alone need not decrease Manhattan distance. -/
theorem exists_solution_of_phase_bounds {P T F S : ℕ}
    (hpreparation : PreparationContract P) (htransport : TransportContract T)
    (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (hfinish : ∀ A : Board (k^4), Arranged hk A →
      ∃ q : Path A (target (k^4)), q.length ≤ F*k^11)
    (hbudget : 274+F ≤ 2*S) (B : Board (k^4)) (hB : Reachable B) :
    ∃ p : Path B (target (k^4)), p.inefficientMoves ≤ (P+T+S)*k^11 ∧
      p.length ≤ manhattan B + 2*(P+T+S)*k^11 := by
  apply ((hpreparation k hk).comp (htransport k hk)).exists_solution ?_ B hB
  intro A hA
  obtain ⟨D,p,hp,hblank,hsorted,_⟩ :=
    exists_arrangement_path hk A hA.clear hA.sorted
  have hD : Arranged hk D := Arranged.of_path hA.reachable p hsorted (by
    rw [hblank]
    exact reservoir_subset_square hA.blank_last)
  obtain ⟨q,hq⟩ := hfinish D hD
  refine ⟨p.append q,?_⟩
  rw [Path.length_append]
  calc
    p.length+q.length ≤ (274+F)*k^11 := by nlinarith
    _ ≤ (2*S)*k^11 := Nat.mul_le_mul_right _ hbudget

/-- The three proved phases complete the phase package once Transport is supplied. -/
theorem phaseContracts_of_transport {C : ℕ} (h : TransportContract C) :
    FourPhaseContracts ⟨1033,C,3277,374⟩ :=
  ⟨preparationContract,h,arrangeContract,finishContract⟩

/-- A supplied Transport contract combines with the other concrete phases to
give the fourth-power approximation. -/
theorem fourthPowerApproximation_of_transport {C : ℕ} (h : TransportContract C) :
    FourthPowerApproximation := by
  refine ⟨2*(1033+C+2012),?_⟩
  intro k hk
  letI : NeZero (k^4) := ⟨by positivity⟩
  intro B
  obtain ⟨p,_,hp⟩ := exists_solution_of_phase_bounds preparationContract h k hk
    (exists_finish_path hk) (by norm_num : 274+747 ≤ 2*2012) B.val B.property
  exact (optimalLength_le_path_length B p).trans hp

theorem uniformApproximation_of_transport {C : ℕ} (h : TransportContract C) :
    UniformApproximation :=
  uniformApproximation_of_fourthPowerApproximation (fourthPowerApproximation_of_transport h)

open Filter Asymptotics in
/-- Both conclusions of Proposition 9 for any supplied Transport contract. -/
theorem proposition9_of_transport {C : ℕ} (h : TransportContract C) :
    ((fun n : ℕ => averageOptimalLength n - (2 / 3 : ℝ)*(n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) ∧
    ((fun n : ℕ => godsNumber n - (n : ℝ)^3)
      =O[atTop] (fun n : ℕ => Real.rpow (n : ℝ) (11 / 4 : ℝ))) :=
  proposition9_of_fourthPowerApproximation (fourthPowerApproximation_of_transport h)

/-- The four concrete legal phases, with uniform inefficient-move budgets. -/
theorem phaseContracts : FourPhaseContracts ⟨1033,82,3277,374⟩ :=
  phaseContracts_of_transport transportContract

/-- Explicit inefficiency and additive length bounds for the constructed solution. -/
theorem exists_fourth_power_solution (k : ℕ) (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hB : Reachable B) :
    ∃ p : Path B (target (k^4)), p.inefficientMoves ≤ 3127*k^11 ∧
      p.length ≤ manhattan B + 6254*k^11 := by
  exact exists_solution_of_phase_bounds preparationContract transportContract k hk
    (exists_finish_path hk) (by norm_num : 274+747 ≤ 2*2012) B hB

/-- The additive approximation on every sufficiently large fourth-power board. -/
theorem fourthPowerApproximation : FourthPowerApproximation :=
  fourthPowerApproximation_of_transport transportContract

/-- An explicit additive bound for every board dimension at least sixteen. -/
theorem optimalLength_le_manhattan_add {n : ℕ} [NeZero n] (hn : 16 ≤ n)
    (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      14286*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  let : NeZero (k^4) := ⟨by positivity⟩
  have hfourth (A : ReachableBoard (k^4)) :
      optimalLength A ≤ manhattan A.val+6254*k^11 := by
    obtain ⟨p,_,hp⟩ := exists_fourth_power_solution k hk A.val A.property
    exact (optimalLength_le_path_length A p).trans hp
  have h := optimalLength_le_of_fourth_power_bound_rpow B k 6254 hk hlo hhi hfourth
  norm_num at h
  exact h

/-- A legal solution with explicit inefficiency and length bounds for every `n ≥ 16`. -/
theorem exists_solution_with_bound {n : ℕ} [NeZero n] (hn : 16 ≤ n)
    (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 7143*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+14286*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength : (p.length : ℝ) ≤
      (manhattan B.val : ℝ)+14286*Real.rpow (n : ℝ) (11/4 : ℝ) := by
    rw [hp]
    exact optimalLength_le_manhattan_add hn B
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ) = (manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- The uniform additive approximation for arbitrary sufficiently large boards. -/
theorem uniformApproximation : UniformApproximation :=
  uniformApproximation_of_transport transportContract

end SlidingPuzzle.Algorithm
