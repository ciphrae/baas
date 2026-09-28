import SlidingPuzzle.Hub.Layout
import SlidingPuzzle.Algorithm.Finish

/-! # Finish on the hub layout

The formalized Finish (`Algorithm/Finish.lean`) solves each square with a local
solver once every tile lies in its own square. It was stated for `Dims`
(`k³ ≤ s`), but only uses `8 ≤ s`; it is applied here through
`Partition.exists_finish_path_of` (stated for `Partition.FDims`). -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

namespace FinishGen

open _root_.SlidingPuzzle.Partition in
theorem side_eq (hd : HDims n k s) : side n k = s := by
  unfold side
  rw [← hd.mul]
  exact Nat.mul_div_cancel_left s (by have := hd.two_le; omega)

open _root_.SlidingPuzzle.Partition in
theorem toFDims (hd : HDims n k s) : FDims n k :=
  ⟨hd.two_le, by rw [side_eq hd]; have := hd.room; have := hd.two_le; omega, by rw [side_eq hd]; exact hd.mul⟩

private theorem div_eq_iff' {x r s : ℕ} (hs : 0 < s) : x / s = r ↔ r * s ≤ x ∧ x < (r + 1) * s := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self x s, by
      have := Nat.lt_div_mul_add (a := x) hs
      rw [Nat.add_mul, Nat.one_mul]; exact this⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2

open _root_.SlidingPuzzle.Partition in
/-- `Partition.square` is the hub square of a cell. -/
theorem square_iff_sqOf (hd : HDims n k s) (i : GroupIndex k) (x : Cell n) :
    square i x ↔ sqOf hd x = (groupRow i, groupCol i) := by
  have hs : 0 < s := by have := hd.room; omega
  unfold square
  rw [side_eq hd]
  simp only [sqOf, Prod.ext_iff, Fin.ext_iff]
  rw [div_eq_iff' hs, div_eq_iff' hs]
  tauto

end FinishGen

open FinishGen

/-- Finish for a board whose tiles all lie in their own squares. -/
theorem exists_finish (hd : HDims n k s) [NeZero n] {cost ineff : ℕ → ℕ}
    (hsolver : SolverBound cost ineff) (B : Board n) (hB : Reachable B)
    (hsorted : ∀ x, (B x).val ≠ 0 → classOf hd (B x) = sqOf hd x)
    (hblank : IsLast (sqOf hd (blank B))) :
    ∃ p : Path B (target n), p.length ≤ k ^ 2 * cost s + 9354 * k ^ 2 * n := by
  have hf := toFDims hd
  have hS : Partition.SquaresSorted (k := k) B := by
    intro i c hc hnz
    refine (Partition.mem_targetGroup i _).mpr ⟨hnz, ?_⟩
    rw [square_iff_sqOf hd] at hc ⊢
    have h := hsorted c hnz
    unfold classOf at h
    rw [h, hc]
  have hL : Partition.square (Partition.lastGroup k hf) (blank B) := by
    rw [square_iff_sqOf hd]
    simp only [Partition.lastGroup, Partition.groupRow, Partition.groupCol,
      Equiv.symm_apply_apply]
    exact Prod.ext (Fin.ext hblank.1) (Fin.ext hblank.2)
  obtain ⟨p, hp, -⟩ := Partition.exists_finish_path_of hsolver hf B hB hS hL
  exact ⟨p, by rwa [side_eq hd] at hp⟩

end SlidingPuzzle.Hub
