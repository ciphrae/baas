import SlidingPuzzle.Moves.Local

/-! A four-step blank cycle around a local square. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- The board obtained by moving the blank around `a, b, c, d` and back to `a`. -/
def cycleBoard (B : Board n) (a b c d : Cell n) : Board n :=
  swapCells (swapCells (swapCells (swapCells B a b) b c) c d) d a

/-- The four local moves around an adjacent cycle are executable. -/
theorem executes_cycle {B : Board n} {a b c d : Cell n}
    (hblank : blank B = a)
    (hab : gridDistance a b = 1) (hbc : gridDistance b c = 1)
    (hcd : gridDistance c d = 1) (hda : gridDistance d a = 1) :
    Executes B [b, c, d, a] (cycleBoard B a b c d) := by
  subst a
  let B₁ := swapCells B (blank B) b
  have hb₁ : blank B₁ = b := by
    exact blank_swapCells B b
  let B₂ := swapCells B₁ b c
  have hb₂ : blank B₂ = c := by
    change blank (swapCells B₁ b c) = c
    rw [← hb₁]
    exact blank_swapCells B₁ c
  let B₃ := swapCells B₂ c d
  have hb₃ : blank B₃ = d := by
    change blank (swapCells B₂ c d) = d
    rw [← hb₂]
    exact blank_swapCells B₂ d
  let B₄ := swapCells B₃ d (blank B)
  change Executes B [b, c, d, blank B] B₄
  refine .cons hab ?_
  change Executes B₁ [c, d, blank B] B₄
  refine .cons ?_ ?_
  · simpa [hb₁] using hbc
  rw [hb₁]
  change Executes B₂ [d, blank B] B₄
  refine .cons ?_ ?_
  · simpa [hb₂] using hcd
  rw [hb₂]
  change Executes B₃ [blank B] B₄
  refine .cons ?_ ?_
  · simpa [hb₃] using hda
  rw [hb₃]
  exact .nil B₄

/-- Traversing an adjacent four-cycle gives a legal path with four moves. -/
theorem exists_path_cycle {B : Board n} {a b c d : Cell n}
    (hblank : blank B = a)
    (hab : gridDistance a b = 1) (hbc : gridDistance b c = 1)
    (hcd : gridDistance c d = 1) (hda : gridDistance d a = 1) :
    ∃ p : Path B (cycleBoard B a b c d), p.length = 4 := by
  obtain ⟨p, hp⟩ := (executes_cycle hblank hab hbc hcd hda).exists_path
  exact ⟨p, by simpa using hp⟩

/-- The blank returns to its starting cell after the four-cycle. -/
theorem blank_cycle {B : Board n} {a b c d : Cell n}
    (hblank : blank B = a) :
    blank (cycleBoard B a b c d) = a := by
  subst a
  let B₁ := swapCells B (blank B) b
  have hb₁ : blank B₁ = b := by exact blank_swapCells B b
  let B₂ := swapCells B₁ b c
  have hb₂ : blank B₂ = c := by
    change blank (swapCells B₁ b c) = c
    rw [← hb₁]
    exact blank_swapCells B₁ c
  let B₃ := swapCells B₂ c d
  have hb₃ : blank B₃ = d := by
    change blank (swapCells B₂ c d) = d
    rw [← hb₂]
    exact blank_swapCells B₂ d
  change blank (swapCells B₃ d (blank B)) = blank B
  rw [← hb₃]
  exact blank_swapCells B₃ _

/-- A four-cycle changes no cell outside its four vertices. -/
theorem cycle_preserves {B : Board n} {a b c d x : Cell n}
    (hblank : blank B = a)
    (hab : gridDistance a b = 1) (hbc : gridDistance b c = 1)
    (hcd : gridDistance c d = 1) (hda : gridDistance d a = 1)
    (hx : x ∉ ([a, b, c, d] : List (Cell n))) :
    cycleBoard B a b c d x = B x := by
  apply (executes_cycle hblank hab hbc hcd hda).preserves
  · have hxa : x ≠ a := by
      intro hxa
      apply hx
      simp [hxa]
    simpa [hblank] using hxa
  · simpa [or_comm, or_left_comm, or_assoc] using hx

/-- With four distinct vertices, the nonblank contents rotate once around the cycle. -/
theorem cycle_rotate {B : Board n} {a b c d : Cell n}
    (hblank : blank B = a)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    cycleBoard B a b c d a = B a ∧
      cycleBoard B a b c d b = B c ∧
      cycleBoard B a b c d c = B d ∧
      cycleBoard B a b c d d = B b := by
  subst a
  have hba : b ≠ blank B := hab.symm
  have hca : c ≠ blank B := hac.symm
  have hda : d ≠ blank B := had.symm
  have hcb : c ≠ b := hbc.symm
  have hdb : d ≠ b := hbd.symm
  have hdc : d ≠ c := hcd.symm
  simp [cycleBoard, Equiv.swap_apply_def, hab, hba, hac, hca, had, hda,
    hbc, hcb, hbd, hdb, hcd, hdc]

end SlidingPuzzle
