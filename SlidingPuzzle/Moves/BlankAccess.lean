import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Parberry

/-! Blank access with a preservation guarantee outside the endpoint rectangle. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- A shortest blank-access word only changes cells in the rectangle spanned by
its starting and ending cells. -/
theorem exists_blank_access_path_preserving (B : Board n) (c : Cell n) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = c ∧ p.length ≤ gridDistance (blank B) c ∧
      ∀ x : Cell n,
        x.1.val < min (blank B).1.val c.1.val ∨
        max (blank B).1.val c.1.val < x.1.val ∨
        x.2.val < min (blank B).2.val c.2.val ∨
        max (blank B).2.val c.2.val < x.2.val → C x = B x := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  let a := blank B
  let w := Zhong.moveToWord a.1.val a.2.val c.1.val c.2.val
  obtain ⟨p,hp⟩ := path_of_zhong_word B w
  refine ⟨Zhong.actSeq B w,p,?_,?_,?_⟩
  · exact Zhong.blank_actSeq_moveToWord a.1.val a.2.val c.1.val c.2.val
      c.1.isLt c.2.isLt a.1.isLt a.2.isLt B rfl
  · simpa [w, Zhong.length_moveToWord, gridDistance,a] using hp
  · intro x hx
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf a w x) = B x
    congr 1
    apply Zhong.permOf_apply_of_not_mem_traceSet
    intro hmem
    have hr := Zhong.moveToWord_traceSet_row a.1.val a.2.val c.1.val c.2.val
      c.1.isLt c.2.isLt a.1.isLt a.2.isLt x hmem
    have hc := Zhong.moveToWord_traceSet_col a.1.val a.2.val c.1.val c.2.val
      c.1.isLt c.2.isLt a.1.isLt a.2.isLt x hmem
    change _ < min a.1.val c.1.val ∨ max a.1.val c.1.val < _ ∨
      _ < min a.2.val c.2.val ∨ max a.2.val c.2.val < _ at hx
    omega

/-- Vertical-then-horizontal access fixes every cell off the initial column and
the final row. This sharper footprint permits routing around a data rectangle. -/
theorem exists_blank_access_path_elbow (B : Board n) (c : Cell n) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = c ∧ p.length ≤ 2*n ∧
      ∀ x : Cell n, x.2 ≠ (blank B).2 → x.1 ≠ c.1 → C x = B x := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  let a := blank B
  let w := Zhong.moveToWord a.1.val a.2.val c.1.val c.2.val
  obtain ⟨p,hp⟩ := path_of_zhong_word B w
  refine ⟨Zhong.actSeq B w,p,?_,?_,?_⟩
  · exact Zhong.blank_actSeq_moveToWord a.1.val a.2.val c.1.val c.2.val
      c.1.isLt c.2.isLt a.1.isLt a.2.isLt B rfl
  · exact hp.trans (Zhong.length_moveToWord_le _ _ _ _ c.1.isLt a.1.isLt
      c.2.isLt a.2.isLt |>.trans (by omega))
  · intro x hxcol hxrow
    rw [Zhong.actSeq_eq_permOf]
    change B (Zhong.permOf a w x) = B x
    congr 1
    apply Zhong.permOf_apply_of_not_mem_traceSet
    intro hmem
    change x ∈ Zhong.traceSet a (Zhong.moveXWord a.1.val c.1.val ++
      Zhong.moveYWord a.2.val c.2.val) at hmem
    rw [Zhong.traceSet_append] at hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · exact hxcol (Zhong.moveXWord_traceSet _ _ _ c.1.isLt a.1.isLt a.2.isLt x hmem).1
    · have ht := Zhong.trace_moveXWord a.1.val a.2.val c.1.val c.1.isLt a.1.isLt a.2.isLt
      change Zhong.trace a (Zhong.moveXWord a.1.val c.1.val) = (c.1,a.2) at ht
      rw [ht] at hmem
      exact hxrow (Zhong.moveYWord_traceSet _ _ _ c.2.isLt c.1.isLt a.2.isLt x hmem)

end SlidingPuzzle
