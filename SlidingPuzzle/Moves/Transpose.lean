import SlidingPuzzle.Moves.Embedding

/-! Coordinate transposition preserves paths and their lengths. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

def transposeBoard (B : Board n) : Board n := (Equiv.prodComm _ _).trans B

@[simp] theorem transposeBoard_apply (B : Board n) (c : Cell n) :
    transposeBoard B c = B c.swap := rfl

@[simp] theorem blank_transposeBoard (B : Board n) :
    blank (transposeBoard B) = (blank B).swap := rfl

@[simp] theorem transposeBoard_transposeBoard (B : Board n) :
    transposeBoard (transposeBoard B) = B := by ext x; rfl

/-- Transpose a legal path without changing its length. -/
theorem Path.exists_transpose {B C : Board n} (p : Path B C) :
    ∃ q : Path (transposeBoard B) (transposeBoard C), q.length = p.length := by
  obtain ⟨D,q,hq,hD,_⟩ := p.exists_embedded (Equiv.prodComm _ _).toEmbedding
    (fun a b h => by simpa [gridDistance, Nat.add_comm] using h)
    (Function.Embedding.refl _) rfl (transposeBoard B) (fun _ => rfl)
  have he : D = transposeBoard C := by
    apply Equiv.ext
    intro x
    simpa using hD x.swap
  subst D
  exact ⟨q,hq⟩

end SlidingPuzzle
