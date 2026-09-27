import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.JumpAll
import SlidingPuzzle.Moves.Transpose

/-! Local blank/tile jumps in every orientation. The cost depends on the
distance between the endpoints, rather than the side of the whole board. -/
namespace SlidingPuzzle
noncomputable section
open Classical

private def stripEmbedding {n m : ℕ} (r c : ℕ) (hr : r+2 ≤ n) (hc : c+m ≤ n)
    (x : Zhong.Cell 2 m) : Cell n :=
  (⟨r+x.1.val, by have := x.1.isLt; omega⟩,
    ⟨c+x.2.val, by have := x.2.isLt; omega⟩)

private theorem stripEmbedding_injective {n m : ℕ} (r c : ℕ)
    (hr : r+2 ≤ n) (hc : c+m ≤ n) :
    Function.Injective (stripEmbedding r c hr hc) := by
  intro x y h
  have h₁ := congrArg (fun z : Cell n => z.1.val) h
  have h₂ := congrArg (fun z : Cell n => z.2.val) h
  apply Prod.ext <;> apply Fin.ext <;> dsimp [stripEmbedding] at h₁ h₂ <;> omega

private theorem stripEmbedding_neighbor {n m : ℕ} (r c : ℕ)
    (hr : r+2 ≤ n) (hc : c+m ≤ n)
    (x : Zhong.Cell 2 m) (d : Zhong.Dir) (y : Zhong.Cell 2 m)
    (h : Zhong.neighbor? x d = some y) :
    Zhong.neighbor? (stripEmbedding r c hr hc x) d =
      some (stripEmbedding r c hr hc y) := by
  rcases x with ⟨⟨xr, hxr⟩, ⟨xc, hxc⟩⟩
  rcases y with ⟨⟨yr, hyr⟩, ⟨yc, hyc⟩⟩
  dsimp only [stripEmbedding]
  cases d <;> simp only [Zhong.neighbor?] at h ⊢ <;>
    split_ifs at * <;> simp_all only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq,
      true_and, and_true]
  all_goals omega

/-- Opposite-colour endpoints in the same or adjacent rows can be exchanged
with the blank in a thin strip. Every other cell is restored, and the cost is
at most `13*(horizontal distance + 1)`, including all boundary orientations. -/
theorem exists_horizontal_jump {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (B : Board n) (b : Cell n)
    (hrow : Nat.dist (blank B).1.val b.1.val ≤ 1)
    (hcolor : ((blank B).1.val + (blank B).2.val + b.1.val + b.2.val) % 2 = 1) :
    ∃ p : Path B (swapCells B (blank B) b),
      p.length ≤ 13*(Nat.dist (blank B).2.val b.2.val + 1) := by
  let a := blank B
  let r := min (min a.1.val b.1.val) (n-2)
  let c := min a.2.val b.2.val
  let m := Nat.dist a.2.val b.2.val + 1
  have hr : r+2 ≤ n := by dsimp [r]; omega
  have hc : c+m ≤ n := by dsimp [c, m, Nat.dist]; omega
  have har : r ≤ a.1.val ∧ a.1.val < r+2 := by
    change Nat.dist a.1.val b.1.val ≤ 1 at hrow
    dsimp [r, Nat.dist] at *; omega
  have hbr : r ≤ b.1.val ∧ b.1.val < r+2 := by
    change Nat.dist a.1.val b.1.val ≤ 1 at hrow
    dsimp [r, Nat.dist] at *; omega
  have hac : c ≤ a.2.val ∧ a.2.val < c+m := by dsimp [c, m, Nat.dist]; omega
  have hbc : c ≤ b.2.val ∧ b.2.val < c+m := by dsimp [c, m, Nat.dist]; omega
  let x : Zhong.Cell 2 m := (⟨a.1.val-r, by omega⟩, ⟨a.2.val-c, by omega⟩)
  let y : Zhong.Cell 2 m := (⟨b.1.val-r, by omega⟩, ⟨b.2.val-c, by omega⟩)
  have hx : stripEmbedding r c hr hc x = a := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [stripEmbedding, x] <;> omega
  have hy : stripEmbedding r c hr hc y = b := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [stripEmbedding, y] <;> omega
  have hxy : (x.1.val+x.2.val+y.1.val+y.2.val)%2 = 1 := by
    change (a.1.val+a.2.val+b.1.val+b.2.val)%2 = 1 at hcolor
    dsimp [x, y]; omega
  obtain ⟨w, happ, hperm, hlen⟩ := Zhong.strip_jump hxy
  have hlift := Zhong.permOf_map_eq_swap (f := id)
    (stripEmbedding_injective r c hr hc) (stripEmbedding_neighbor r c hr hc) x w happ hperm
  simp only [List.map_id, hx, hy] at hlift
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  have he : Zhong.actSeq B w = swapCells B (blank B) b := by
    rw [Zhong.actSeq_eq_permOf]
    change (Zhong.permOf a w).trans B = _
    rw [hlift]
    rfl
  have hpath := path_of_zhong_word B w
  rw [he] at hpath
  obtain ⟨p, hp⟩ := hpath
  have hlen' : w.length ≤ 13 * (Nat.dist (blank B).2.val b.2.val + 1) := by
    dsimp [m, a] at hlen ⊢
    omega
  exact ⟨p, hp.trans hlen'⟩

@[simp] theorem transposeBoard_swapCells {n : ℕ} [NeZero n] (B : Board n) (a b : Cell n) :
    transposeBoard (swapCells B a b) = swapCells (transposeBoard B) a.swap b.swap := by
  ext x
  simp only [transposeBoard_apply, swapCells_apply]
  congr 1
  have h := Zhong.swap_apply_injective (Equiv.prodComm (Fin n) (Fin n)).injective a b x.swap
  simpa using congrArg Prod.swap h.symm

/-- The vertical form of the local jump, with the same distance-sensitive
cost and exact two-cell endpoint effect. -/
theorem exists_vertical_jump {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (B : Board n) (b : Cell n)
    (hcol : Nat.dist (blank B).2.val b.2.val ≤ 1)
    (hcolor : ((blank B).1.val + (blank B).2.val + b.1.val + b.2.val) % 2 = 1) :
    ∃ p : Path B (swapCells B (blank B) b),
      p.length ≤ 13*(Nat.dist (blank B).1.val b.1.val + 1) := by
  obtain ⟨p, hp⟩ := exists_horizontal_jump hn (transposeBoard B) b.swap hcol (by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcolor)
  have hout : ∃ q : Path (transposeBoard (transposeBoard B))
      (transposeBoard (swapCells (transposeBoard B) (blank (transposeBoard B)) b.swap)),
      q.length ≤ 13*(Nat.dist (blank B).1.val b.1.val + 1) := by
    obtain ⟨q, hq⟩ := p.exists_transpose
    exact ⟨q, hq.le.trans hp⟩
  rw [transposeBoard_swapCells, transposeBoard_transposeBoard,
    blank_transposeBoard, Prod.swap_swap, Prod.swap_swap] at hout
  exact hout

end
end SlidingPuzzle
