import SlidingPuzzle.Moves.Cycle

/-! The terminal move that places the final two tiles of a row after they have
been staged in the right-hand column of a two-by-two patch. -/
namespace SlidingPuzzle.Parberry
variable {n : ℕ} [NeZero n]

/-- Place a staged row-ending pair in four legal moves, return the blank below
it, and preserve every cell outside the terminal two-by-two patch. -/
theorem exists_row_end_path (B : Board n) (r c : ℕ)
    (hr : r+1<n) (hc : c+1<n)
    (hb : blank B = (⟨r+1,hr⟩,⟨c,by omega⟩)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length = 4 ∧ blank C = blank B ∧
      C (⟨r,by omega⟩,⟨c,by omega⟩) = B (⟨r,by omega⟩,⟨c+1,hc⟩) ∧
      C (⟨r,by omega⟩,⟨c+1,hc⟩) = B (⟨r+1,hr⟩,⟨c+1,hc⟩) ∧
      ∀ z, z.1.val<r ∨ r+1<z.1.val ∨ z.2.val<c ∨ c+1<z.2.val → C z=B z := by
  let a : Cell n := (⟨r+1,hr⟩,⟨c,by omega⟩)
  let b : Cell n := (⟨r,by omega⟩,⟨c,by omega⟩)
  let d : Cell n := (⟨r,by omega⟩,⟨c+1,hc⟩)
  let e : Cell n := (⟨r+1,hr⟩,⟨c+1,hc⟩)
  have hab : gridDistance a b=1 := by simp [a,b,gridDistance,Nat.dist]
  have hbd : gridDistance b d=1 := by simp [b,d,gridDistance,Nat.dist]
  have hde : gridDistance d e=1 := by simp [d,e,gridDistance,Nat.dist]
  have hea : gridDistance e a=1 := by simp [e,a,gridDistance,Nat.dist]
  obtain ⟨p,hp⟩ := exists_path_cycle hb hab hbd hde hea
  have hrotate := cycle_rotate hb
    (show a≠b by simp [a,b]) (show a≠d by simp [a,d]) (show a≠e by simp [a,e])
    (show b≠d by simp [b,d]) (show b≠e by simp [b,e]) (show d≠e by simp [d,e])
  refine ⟨cycleBoard B a b d e,p,hp,(blank_cycle hb).trans hb.symm,
    hrotate.2.1,hrotate.2.2.1,?_⟩
  intro z hz
  apply cycle_preserves hb hab hbd hde hea
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  dsimp [a,b,d,e]
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> subst z <;> simp only [Fin.val_mk] at hz <;> omega
end SlidingPuzzle.Parberry
