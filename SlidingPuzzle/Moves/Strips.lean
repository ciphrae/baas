import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Lift

/-! Concrete legal paths for blank access and strip transpositions. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Move the blank to any prescribed cell within its Manhattan distance. -/
theorem exists_blank_access_path (B : Board n) (c : Cell n) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = c ∧ p.length ≤ gridDistance (blank B) c := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  let a := blank B
  let w := Zhong.moveToWord a.1.val a.2.val c.1.val c.2.val
  obtain ⟨p,hp⟩ := path_of_zhong_word B w
  refine ⟨Zhong.actSeq B w,p,?_,?_⟩
  · exact Zhong.blank_actSeq_moveToWord a.1.val a.2.val c.1.val c.2.val
      c.1.isLt c.2.isLt a.1.isLt a.2.isLt B rfl
  · simpa [w, Zhong.length_moveToWord, gridDistance,a] using hp

/-- A horizontal strip swaps just the blank and the opposite-row tile at offset `2*l`. -/
theorem exists_horizontal_strip_swap (B : Board n) (r : ℕ) (hr : r+1<n)
    (c : Fin n) (l : ℕ) (hc : c.val+2*l<n)
    (hb : blank B = (⟨r, by omega⟩, c)) :
    ∃ p : Path B (swapCells B (⟨r, by omega⟩,c) (⟨r+1,hr⟩,⟨c.val+2*l,hc⟩)),
      p.length ≤ 20*l+1 := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  have he := Zhong.hStrip_jumpWord_effect r hr l hc B hb
  have h := path_of_zhong_word B (Zhong.jumpWord l)
  rw [he] at h
  simpa [swapCells,Zhong.hStrip,Zhong.top,Zhong.bot,Zhong.jumpWord_length] using h

/-- The transposed strip construction swaps the blank with an opposite-column tile. -/
theorem exists_vertical_strip_swap (B : Board n) (r : ℕ) (hr : r+1<n)
    (c : Fin n) (l : ℕ) (hc : c.val+2*l<n)
    (hb : blank B = (c,⟨r, by omega⟩)) :
    ∃ p : Path B (swapCells B (c,⟨r, by omega⟩) (⟨c.val+2*l,hc⟩,⟨r+1,hr⟩)),
      p.length ≤ 20*l+1 := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  have he := Zhong.vStrip_transJumpWord_effect r hr l hc B hb
  have h := path_of_zhong_word B (Zhong.transJumpWord l)
  rw [he] at h
  simpa [swapCells,Zhong.vStrip,Zhong.top,Zhong.bot,Zhong.transJumpWord,
    Zhong.jumpWord_length] using h
/-- A horizontal strip swaps just the blank and the same-row tile at odd offset `2*l+1`. -/
theorem exists_horizontal_odd_swap (B : Board n) (r : ℕ) (hr : r+1<n)
    (c : Fin n) (l : ℕ) (hc : c.val+2*l+1<n)
    (hb : blank B = (⟨r, by omega⟩, c)) :
    ∃ p : Path B (swapCells B (⟨r, by omega⟩,c) (⟨r,by omega⟩,⟨c.val+2*l+1,hc⟩)),
      p.length ≤ 24*l+1 := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  have he := Zhong.hStrip_row0Word_effect r hr l hc B hb
  have h := path_of_zhong_word B (Zhong.row0Word l)
  rw [he] at h
  simpa [swapCells,Zhong.hStrip,Zhong.top,Zhong.bot,Zhong.row0Word_length] using h

/-- The transposed strip construction swaps the blank with an same-column tile at odd offset. -/
theorem exists_vertical_odd_swap (B : Board n) (r : ℕ) (hr : r+1<n)
    (c : Fin n) (l : ℕ) (hc : c.val+2*l+1<n)
    (hb : blank B = (c,⟨r, by omega⟩)) :
    ∃ p : Path B (swapCells B (c,⟨r, by omega⟩) (⟨c.val+2*l+1,hc⟩,⟨r,by omega⟩)),
      p.length ≤ 24*l+1 := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  have he := Zhong.vStrip_transRow0Word_effect r hr l hc B hb
  have h := path_of_zhong_word B (Zhong.transRow0Word l)
  rw [he] at h
  simpa [swapCells,Zhong.vStrip,Zhong.top,Zhong.bot,Zhong.transRow0Word,
    Zhong.row0Word_length] using h
end SlidingPuzzle
