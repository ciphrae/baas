import SlidingPuzzle.Moves.BorrowedSolve
import SlidingPuzzle.Moves.BlockCorner
import SlidingPuzzle.Moves.Exchange

/-! Finish one block, putting any parity correction into two external buffer cells. -/
namespace SlidingPuzzle
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- A closed nonblank block can be completely solved with a cubic local cost.
At most the two external buffer tiles are exchanged; all other outside cells
and the blank return to their initial state. -/
theorem exists_block_finish_of_solver {K : ℕ} (hsolver : CubicSolverBound K)
    (B T : Board n) (hm : 8 ≤ m) (hn : 4 ≤ n)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (u v : Cell n) (huv : u ≠ v)
    (hu : u ∉ Set.range (blockEmbedding ro co hr hc))
    (hv : v ∉ Set.range (blockEmbedding ro co hr hc))
    (hu0 : B u ≠ 0) (hv0 : B v ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ K*m^3+9352*n ∧ blank C = blank B ∧
      (∀ c, C (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc c)) ∧
      ((C u = B u ∧ C v = B v) ∨ (C u = B v ∧ C v = B u)) ∧
      (∀ x, x ∉ Set.range (blockEmbedding ro co hr hc) → x ≠ u → x ≠ v → C x = B x) := by
  classical
  let ι := blockEmbedding ro co hr hc
  let z := blank (target m)
  let a : Cell m := (0,0)
  let b : Cell m := (0,⟨1,by omega⟩)
  have haz : a ≠ z := by
    intro h
    have hh := congrArg (fun x : Cell m => x.1.val) h
    dsimp [z] at hh
    rw [blank_target_eq] at hh
    change 0=m-1 at hh
    omega
  have hbz : b ≠ z := by
    intro h
    have hh := congrArg (fun x : Cell m => x.1.val) h
    dsimp [z] at hh
    rw [blank_target_eq] at hh
    change 0=m-1 at hh
    omega
  have hab : a ≠ b := by simp [a,b,Fin.ext_iff]
  obtain ⟨D,p,hp,hbD,hDz,hDlabels,hDfix⟩ := exists_correct_block_corner B T hn ι z a b
    haz.symm hbz.symm hab hzero hlabels
  obtain ⟨E,q,hq,hbE,hE,hEfix⟩ := exists_borrowed_solution_of_solver hsolver D T hm ro co hr hc
    (hbD.trans hb) hzero hDlabels hDz a b hab haz hbz
  have hout (x : Cell n) (hx : x ∉ Set.range ι) : E x = B x :=
    (hEfix x hx).trans (hDfix x hx)
  have hEu : E u=B u := hout u hu
  have hEv : E v=B v := hout v hv
  rcases hE with hE | hE
  · refine ⟨E,p.append q,?_,hbE.trans hbD,hE,Or.inl ⟨hEu,hEv⟩,?_⟩
    · rw [Path.length_append]; omega
    · intro x hx _ _; exact hout x hx
  · have hau : ι a ≠ u := fun h => hu ⟨a,h⟩
    have hav : ι a ≠ v := fun h => hv ⟨a,h⟩
    have hbu : ι b ≠ u := fun h => hu ⟨b,h⟩
    have hbv : ι b ≠ v := fun h => hv ⟨b,h⟩
    have hEa : E (ι a)=T (ι b) := by simpa using hE a
    have hEb : E (ι b)=T (ι a) := by simpa using hE b
    obtain ⟨C,s,hs,hbC,hCa,hCu,hCb,hCv,hfix⟩ := exists_double_swap E hn
      (ι a) u (ι b) v hau (ι.injective.ne hab) hav hbu.symm huv hbv
      (by rw [hEa]; exact hzero b) (by rwa [hEu])
      (by rw [hEb]; exact hzero a) (by rwa [hEv])
    refine ⟨C,(p.append q).append s,?_,hbC.trans (hbE.trans hbD),?_,
      Or.inr ⟨hCu.trans hEv,hCv.trans hEu⟩,?_⟩
    · simp only [Path.length_append]; omega
    · intro c
      by_cases hca : c=a
      · subst c; exact hCa.trans hEb
      by_cases hcb : c=b
      · subst c; exact hCb.trans hEa
      rw [hfix _ (ι.injective.ne hca) (fun h => hu ⟨c,h⟩)
        (ι.injective.ne hcb) (fun h => hv ⟨c,h⟩),hE,
        Equiv.swap_apply_of_ne_of_ne hca hcb]
    · intro x hx hxu hxv
      rw [hfix x (fun h => hx ⟨a,h.symm⟩) hxu (fun h => hx ⟨b,h.symm⟩) hxv]
      exact hout x hx

/-- Specialize the solver-parametric construction to the checked cubic solver. -/
theorem exists_block_finish (B T : Board n) (hm : 8 ≤ m) (hn : 4 ≤ n)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (u v : Cell n) (huv : u ≠ v)
    (hu : u ∉ Set.range (blockEmbedding ro co hr hc))
    (hv : v ∉ Set.range (blockEmbedding ro co hr hc))
    (hu0 : B u ≠ 0) (hv0 : B v ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 527*m^3+9352*n ∧ blank C = blank B ∧
      (∀ c, C (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc c)) ∧
      ((C u = B u ∧ C v = B v) ∨ (C u = B v ∧ C v = B u)) ∧
      (∀ x, x ∉ Set.range (blockEmbedding ro co hr hc) → x ≠ u → x ≠ v → C x = B x) := by
  exact exists_block_finish_of_solver cubicSolverBound_current B T hm hn ro co hr hc hb hzero hlabels u v huv hu hv hu0 hv0

end SlidingPuzzle
