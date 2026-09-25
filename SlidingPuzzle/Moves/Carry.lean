import SlidingPuzzle.Moves.Local

/-! Explicit blank words: the final blank position, and executability of any
adjacent chain. -/
namespace SlidingPuzzle
noncomputable section

variable {n : ℕ} [NeZero n]

namespace Executes

/-- The blank finishes on the last visited cell. -/
theorem blank_last {B C : Board n} {cs : List (Cell n)} (h : Executes B cs C) :
    blank C = cs.getLast?.getD (blank B) := by
  induction h with
  | nil => rfl
  | @cons B C c cs _ _ ih =>
    rw [ih, blank_swapCells]
    cases cs <;> simp [List.getLast?_cons]

/-- Any adjacent chain of blank destinations is executable. -/
theorem exists_of_chain (B : Board n) (cs : List (Cell n))
    (h : List.IsChain (fun a b : Cell n => gridDistance a b = 1) (blank B :: cs)) :
    ∃ C, Executes B cs C := by
  induction cs generalizing B with
  | nil => exact ⟨B, .nil B⟩
  | cons c cs ih =>
    rw [List.isChain_cons_cons] at h
    obtain ⟨C, hC⟩ := ih (swapCells B (blank B) c) (by rw [blank_swapCells]; exact h.2)
    exact ⟨C, .cons h.1 hC⟩

end Executes

end
end SlidingPuzzle
