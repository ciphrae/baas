import SlidingPuzzle.Algorithm.ParberryProjection
import SlidingPuzzle.Algorithm.Parberry.Prefix

/-! A protected row/column prefix is used both to stage the fourth-power
algorithm and to reduce arbitrary dimensions to a fourth power. The faster
prefix hypothesis below is kept explicit until its path construction is proved. -/
namespace SlidingPuzzle
noncomputable section

/-- A prefix constant `P` contributes `8P` to the arbitrary-size real-power
bound: twice the path cost, and at most four units of outer width. -/
theorem optimalLength_le_of_prefix_bound_rpow {P n k K : ℕ} [NeZero n]
    (hprefix : PrefixPathBound P) (B : ReachableBoard n) (hk : 2 ≤ k)
    (hlo : k^4 ≤ n) (hhi : n < (k+1)^4)
    (hfourth : letI : NeZero (k^4) := ⟨by positivity⟩
      ∀ A : ReachableBoard (k^4), optimalLength A ≤ manhattan A.val + K*k^11) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      ((K : ℝ)+8*(P : ℝ))*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  letI : NeZero (k^4) := ⟨by positivity⟩
  have hk4 : 4 ≤ k^4 := by nlinarith [Nat.pow_le_pow_left hk 4]
  obtain ⟨C,p,hp,hC⟩ := hprefix B.val (target n) rfl (n-k^4) (by omega)
  have hd : n-k^4+k^4=n := Nat.sub_add_cancel hlo
  obtain ⟨A,hA⟩ := exists_residual_board (n-k^4) hd C hC
  have hreachC : Reachable C := by
    obtain ⟨r⟩ := B.property
    exact ⟨r.append p⟩
  have hreachA : Reachable A :=
    residual_reachable (by omega : 2 ≤ k^4) (n-k^4) hd C hC A hA hreachC
  let R : ReachableBoard (k^4) := ⟨A,hreachA⟩
  obtain ⟨q,hq⟩ := shortest_witness R
  have hbound : q.length ≤ manhattan A + K*k^11 := by
    rw [hq]
    exact hfourth R
  have hpath := optimalLength_le_prefix_residual_solution B (n-k^4) hd C p hC A hA q hbound
  have hnat : optimalLength B ≤ manhattan B.val + K*k^11 +
      2*P*((n-k^4)*n^2) := by nlinarith [hp, hpath]
  have hreal : (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      (K : ℝ)*(k : ℝ)^11 + 2*(P : ℝ)*((n-k^4 : ℕ)*(n : ℝ)^2) := by
    exact_mod_cast hnat
  have hscaled := mul_le_mul_of_nonneg_left
    (pow_eleven_le_rpow_of_fourth_power_le hlo) (Nat.cast_nonneg K)
  have hbudget := outer_layer_budget_le_rpow hlo hhi
  have hprefixBudget := mul_le_mul_of_nonneg_left hbudget
    (by positivity : 0 ≤ (2*(P : ℝ)))
  nlinarith

namespace Algorithm

/-- A finish length bound lets the shared-prefix estimate charge arrangement
and finishing together, at half their combined length. -/
theorem optimalLength_le_of_shared_prefix_finish_path {P F S : ℕ}
    (hprefix : PrefixPathBound P)
    (hfinish : ∀ k : ℕ, ∀ hk : 2 ≤ k,
      letI : NeZero (k^4) := ⟨by positivity⟩
      ∀ A : Board (k^4), Partition.Arranged hk A →
        ∃ q : Path A (target (k^4)), q.length ≤ F*k^11)
    (hbudget : 274+F ≤ 2*S)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      ((2*(P+29+82+S)+8*P : ℕ) : ℝ)*
        Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  letI : NeZero (k^4) := ⟨by positivity⟩
  have hfourth (A : ReachableBoard (k^4)) :
      optimalLength A ≤ manhattan A.val+(2*(P+29+82+S))*k^11 := by
    obtain ⟨p,_,hp⟩ := exists_solution_of_phase_bounds
      (preparationContract_of_prefix_bound hprefix) transportContract k hk
      (hfinish k hk) hbudget A.val A.property
    exact (optimalLength_le_path_length A p).trans hp
  have h := optimalLength_le_of_prefix_bound_rpow hprefix B hk hlo hhi hfourth
  convert h using 1 <;> norm_num

/-- A faster protected prefix improves Preparation and the arbitrary-size
reduction simultaneously. The Finish budget is independent. -/
theorem optimalLength_le_of_shared_prefix {P C : ℕ}
    (hprefix : PrefixPathBound P) (hfinish : FinishContract C)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      ((2*(P+29+82+3277+C)+8*P : ℕ) : ℝ)*
        Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨k,hk,hlo,hhi,_⟩ := exists_fourth_power_dimension hn
  letI : NeZero (k^4) := ⟨by positivity⟩
  let contracts : FourPhaseContracts ⟨P+29,82,3277,C⟩ :=
    ⟨preparationContract_of_prefix_bound hprefix,transportContract,arrangeContract,hfinish⟩
  have hfourth (A : ReachableBoard (k^4)) :
      optimalLength A ≤ manhattan A.val+(2*(P+29+82+3277+C))*k^11 := by
    obtain ⟨p,hp⟩ := contracts.exists_solution k hk A.val A.property
    exact (optimalLength_le_path_length A p).trans hp
  have h := optimalLength_le_of_prefix_bound_rpow hprefix B hk hlo hhi hfourth
  convert h using 1 <;> norm_num

/-- The same conditional bound gives an explicit legal solution and its
inefficient-move count. -/
theorem exists_solution_of_shared_prefix {P C : ℕ}
    (hprefix : PrefixPathBound P) (hfinish : FinishContract C)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤
        ((P+29+82+3277+C+4*P : ℕ) : ℝ)*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ) +
        ((2*(P+29+82+3277+C)+8*P : ℕ) : ℝ)*
          Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength : (p.length : ℝ) ≤ (manhattan B.val : ℝ) +
      ((2*(P+29+82+3277+C)+8*P : ℕ) : ℝ)*
        Real.rpow (n : ℝ) (11/4 : ℝ) := by
    rw [hp]
    exact optimalLength_le_of_shared_prefix hprefix hfinish hn B
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ) =
      (manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  norm_num at *
  nlinarith

/-- With the current Finish contract, a `15*d*n²` protected prefix would
already lower the arbitrary-size additive coefficient to `4396`. -/
theorem optimalLength_le_shared_prefix_current_finish
    (hprefix : PrefixPathBound 15)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      4396*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_of_shared_prefix_finish_path hprefix
    (fun k hk => by
      letI : NeZero (k^4) := ⟨by positivity⟩
      exact Partition.exists_finish_path hk)
    (by norm_num : 274+747 ≤ 2*2012) hn B
  norm_num at h
  exact h

/-- Combining the faster prefix with an actual `225*k^11` finishing path
retains the saving from accounting for the whole solving suffix. -/
theorem optimalLength_le_shared_prefix_fast_finish
    (hprefix : PrefixPathBound 15) (hfinish : FastFinishPath)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      3874*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_of_shared_prefix_finish_path hprefix hfinish
    (by norm_num : 274+225 ≤ 2*1751) hn B
  norm_num at h
  exact h

/-- A single constructed Parberry layer routine supplies both the fifteen-
quadratic prefix and the five-cubic solver needed for this projection. -/
theorem optimalLength_le_of_parberry_layer (h : Parberry.LayerPathBound)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      3874*Real.rpow (n : ℝ) (11/4 : ℝ) :=
  optimalLength_le_shared_prefix_fast_finish (Parberry.prefixPathBound_of_layer h)
    (fastFinishPath_of_layer h) hn B

/-- The same single layer hypothesis gives legal witnesses and their
inefficient-move counts. -/
theorem exists_solution_of_parberry_layer (h : Parberry.LayerPathBound)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    ∃ p : Path B.val (target n),
      (p.inefficientMoves : ℝ) ≤ 1937*Real.rpow (n : ℝ) (11/4 : ℝ) ∧
      (p.length : ℝ) ≤ (manhattan B.val : ℝ)+3874*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  obtain ⟨p,hp⟩ := shortest_witness B
  have hlength : (p.length : ℝ) ≤
      (manhattan B.val : ℝ)+3874*Real.rpow (n : ℝ) (11/4 : ℝ) := by
    rw [hp]
    exact optimalLength_le_of_parberry_layer h hn B
  refine ⟨p,?_,hlength⟩
  have hbalance : (p.length : ℝ) =
      (manhattan B.val : ℝ)+2*(p.inefficientMoves : ℝ) := by
    exact_mod_cast p.solution_length
  linarith

/-- The older estimate remains available from an inefficient-move contract
alone; `optimalLength_le_shared_prefix_fast_finish` uses a path length bound. -/
theorem optimalLength_le_shared_prefix_projection
    (hprefix : PrefixPathBound 15) (hfinish : FinishContract 113)
    {n : ℕ} [NeZero n] (hn : 16 ≤ n) (B : ReachableBoard n) :
    (optimalLength B : ℝ) ≤ (manhattan B.val : ℝ) +
      7152*Real.rpow (n : ℝ) (11/4 : ℝ) := by
  have h := optimalLength_le_of_shared_prefix hprefix hfinish hn B
  norm_num at h
  exact h

end Algorithm
end
end SlidingPuzzle
