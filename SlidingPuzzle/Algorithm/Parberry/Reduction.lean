import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Moves.Placement
import Zhong.Algorithm.TwoByTwo

/-! Recursive assembly for a five-cubic Parberry solver.
The outstanding geometric construction is a cheap protected first row and column.
This file proves the base case and the complete recursion from that local input;
it does not assert that the local input has been constructed. -/
namespace SlidingPuzzle.Parberry

/-- The layer construction must solve the first row and column while leaving
an unrestricted residual square. This signed-free budget is exactly the gap
between the cubic budgets at side `n` and side `n-1`. -/
def LayerPathBound : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n),
    letI : NeZero n := ⟨by omega⟩
    ∀ B : Board n, ∃ C : Board n, ∃ p : Path B C,
      p.length+15*n ≤ 15*n^2+5 ∧
      ∀ x y : Fin n, x.val<1 ∨ y.val<1 → C (x,y)=target n (x,y)

/-- The checked two-by-two table gives the recursive base case. -/
theorem exists_solution_two (B : ReachableBoard 2) :
    ∃ p : Path B.val (target 2), p.length ≤ 6 := by
  obtain ⟨q⟩ := exists_solution B
  obtain ⟨word,hlen,hword⟩ := Zhong.solve2x2 B.val (zhong_reachable_of_path q)
  have hp := path_of_zhong_word B.val word
  rw [hword] at hp
  obtain ⟨p,hp⟩ := hp
  exact ⟨p,hp.trans hlen⟩

/-- Once the protected layer routine is built, recursion supplies actual legal
solutions of length at most `5*n^3`, including residual reachability and lifting. -/
theorem exists_solution_of_layer (hlayer : LayerPathBound) :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n, ∃ p : Path B.val (target n), p.length ≤ 5*n^3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    letI : NeZero n := ⟨by omega⟩
    intro B
    by_cases hn2 : n=2
    · subst n
      obtain ⟨p,hp⟩ := exists_solution_two B
      exact ⟨p,by norm_num; omega⟩
    have hn3 : 3 ≤ n := by omega
    let m := n-1
    have hm : 2 ≤ m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    have hd : 1+m=n := by dsimp [m]; omega
    letI : NeZero m := ⟨by omega⟩
    obtain ⟨C,p,hp,hC⟩ := hlayer n hn3 B.val
    obtain ⟨R,hR⟩ := exists_residual_board 1 hd C hC
    have hreachC : Reachable C := by
      obtain ⟨r⟩ := B.property
      exact ⟨r.append p⟩
    have hreachR : Reachable R := residual_reachable hm 1 hd C hC R hR hreachC
    obtain ⟨q,hq⟩ := ih m hmn hm ⟨R,hreachR⟩
    obtain ⟨s,hs⟩ := residual_solution_lifts 1 hd C hC R hR q
    refine ⟨p.append s,?_⟩
    rw [Path.length_append,hs]
    have hcube : 5*n^3+15*n = 5*m^3+15*n^2+5 := by
      rw [show n=m+1 by omega]
      ring
    omega

/-- The precise local construction above suffices for the solver interface used
by all parity correction and block-finishing theorems. -/
theorem cubicSolverBound_of_layer (h : LayerPathBound) : CubicSolverBound 5 := by
  intro n _ hn B
  exact exists_solution_of_layer h n (by omega) B

/-- The paper's layer estimate is stronger than the cubic-gap budget. -/
theorem layer_budget_of_paper {n L : ℕ} (hn : 3 ≤ n)
    (h : L+24*n ≤ 15*n^2+19) : L+15*n ≤ 15*n^2+5 := by
  omega
end SlidingPuzzle.Parberry
