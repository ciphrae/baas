import SlidingPuzzle.Algorithm.Parberry.ColumnSolve
import SlidingPuzzle.Algorithm.Parberry.RowSolve
import SlidingPuzzle.Algorithm.ResidualReachability
import SlidingPuzzle.Moves.Placement
import Zhong.Algorithm.TwoByTwo

/-! A constructed Parberry solver with leading coefficient five.
The boundary routines give an explicit quadratic remainder. This theorem is
unconditional and does not use the stronger, still separate `LayerPathBound`.
-/
namespace SlidingPuzzle.Parberry

/-- Solve a complete outer layer, retaining an unrestricted residual square. -/
theorem exists_layer {n : ℕ} [NeZero n] (hn : 5 ≤ n) (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 15*n^2+3002*n+1 ∧
      ∀ x y : Fin n, x.val<1 ∨ y.val<1 → C (x,y)=target n (x,y) := by
  obtain ⟨D,p,hp,_,hrow⟩ := exists_complete_row B 0 (by omega) (by omega) (by intros; omega)
  obtain ⟨C,q,hq,hfix,hcol⟩ := exists_complete_column D hn hrow
  refine ⟨C,p.append q,?_,?_⟩
  · rw [Path.length_append]; omega
  · intro x y hxy
    rcases hxy with hx | hy
    · have he : x=0 := Fin.ext (by simpa using (show x.val=0 by omega))
      rw [he,hfix]
      simpa using hrow y
    · have he : y=0 := Fin.ext (by simpa using (show y.val=0 by omega))
      rw [he,hcol]

/-- Recursive construction of the paper's `5*n³+O(n²)` move bound.
The explicit remainder absorbs both the boundary routines and the checked
four-by-four base case. -/
theorem exists_solution_cubic_aux :
    ∀ (n : ℕ) (hn : 4 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∀ B : ReachableBoard n, ∃ p : Path B.val (target n),
        2*p.length ≤ 10*n^3+3017*n^2+3009*n+9592 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    letI : NeZero n := ⟨by omega⟩
    intro B
    by_cases hn4 : n=4
    · subst n
      obtain ⟨p,hp⟩ := SlidingPuzzle.exists_solution_cubic_exact B (by omega)
      refine ⟨p,?_⟩
      norm_num at hp ⊢
      omega
    have hn5 : 5 ≤ n := by omega
    let m := n-1
    have hm : 4 ≤ m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    have hd : 1+m=n := by dsimp [m]; omega
    letI : NeZero m := ⟨by omega⟩
    obtain ⟨C,p,hp,hC⟩ := exists_layer hn5 B.val
    obtain ⟨R,hR⟩ := exists_residual_board 1 hd C hC
    have hreachC : Reachable C := by
      obtain ⟨r⟩ := B.property
      exact ⟨r.append p⟩
    have hreachR : Reachable R := residual_reachable (by omega) 1 hd C hC R hR hreachC
    obtain ⟨q,hq⟩ := ih m hmn hm ⟨R,hreachR⟩
    obtain ⟨s,hs⟩ := residual_solution_lifts 1 hd C hC R hR q
    refine ⟨p.append s,?_⟩
    rw [Path.length_append,hs]
    have hgap : 10*m^3+3017*m^2+3009*m+9592+2*(15*n^2+3002*n+1) =
        10*n^3+3017*n^2+3009*n+9592 := by
      rw [show n=m+1 by omega]
      ring
    omega

/-- An actual legal solution with Parberry's leading cubic coefficient. -/
theorem exists_solution_cubic {n : ℕ} [NeZero n] (B : ReachableBoard n) (hn : 4 ≤ n) :
    ∃ p : Path B.val (target n), p.length ≤ 5*n^3+1509*n^2+1505*n+4796 := by
  obtain ⟨p,hp⟩ := exists_solution_cubic_aux n hn B
  exact ⟨p,by omega⟩

end SlidingPuzzle.Parberry
