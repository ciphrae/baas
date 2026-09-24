import SlidingPuzzle.Moves.Local

/-! Explicit blank walks along a row and the five-move tile carry. The carry
moves one tile a unit to the left using two adjacent rows; every other visited
cell is only reported to lie in those rows. -/
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

/-- Walk the blank rightwards along one row. -/
theorem exists_row_walk (B : Board n) (R : Fin n) (a d : ℕ) (had : a + d < n)
    (hblank : blank B = (R, ⟨a, by omega⟩)) :
    ∃ C cs, Executes B cs C ∧ cs.length = d ∧ blank C = (R, ⟨a+d, had⟩) ∧
      ∀ x ∈ cs, x.1 = R ∧ a < x.2.val ∧ x.2.val ≤ a+d := by
  induction d generalizing a B with
  | zero => exact ⟨B, [], .nil B, rfl, hblank, by simp⟩
  | succ d ih =>
    let c : Cell n := (R, ⟨a+1, by omega⟩)
    have hd : gridDistance (blank B) c = 1 := by
      rw [hblank]; simp [gridDistance, c, Nat.dist]
    obtain ⟨C, cs, hC, hlen, hb, hin⟩ :=
      ih (a := a+1) (B := swapCells B (blank B) c) (by omega) (blank_swapCells B c)
    refine ⟨C, c :: cs, .cons hd hC, by simp [hlen], ?_, ?_⟩
    · rw [hb]; congr 2; omega
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, by simp [c], by simp [c]⟩
      · have := hin x hx; omega

/-- Repeated five-move carries. The blank starts immediately left of the tile
in row `R`; `H` is an adjacent helper row. After `m` carries the tile has moved
`m` cells left and the blank is again immediately to its left. -/
theorem exists_carry (B : Board n) (R H : Fin n) (hRH : Nat.dist R.val H.val = 1)
    (w m : ℕ) (hw : w + m + 1 < n)
    (hblank : blank B = (R, ⟨w+m, by omega⟩)) :
    ∃ C cs, Executes B cs C ∧ cs.length = 5*m ∧
      blank C = (R, ⟨w, by omega⟩) ∧
      C (R, ⟨w+1, by omega⟩) = B (R, ⟨w+m+1, hw⟩) ∧
      ∀ x ∈ cs, (x.1 = R ∨ x.1 = H) ∧ w ≤ x.2.val ∧ x.2.val ≤ w+m+1 := by
  induction m generalizing B with
  | zero =>
    refine ⟨B, [], .nil B, rfl, hblank, ?_, by simp⟩
    rfl
  | succ m ih =>
    let c₁ : Cell n := (R, ⟨w+m+2, by omega⟩)
    let c₂ : Cell n := (H, ⟨w+m+2, by omega⟩)
    let c₃ : Cell n := (H, ⟨w+m+1, by omega⟩)
    let c₄ : Cell n := (H, ⟨w+m, by omega⟩)
    let c₅ : Cell n := (R, ⟨w+m, by omega⟩)
    have hRH' : R ≠ H := by intro h; subst h; simp [Nat.dist] at hRH
    have hRHv : R.val ≠ H.val := fun h => hRH' (Fin.ext h)
    have h₁ : gridDistance (blank B) c₁ = 1 := by
      rw [hblank]; simp [gridDistance, c₁, Nat.dist] <;> omega
    let B₁ := swapCells B (blank B) c₁
    have hb₁ : blank B₁ = c₁ := blank_swapCells B c₁
    have hchain : List.IsChain (fun a b : Cell n => gridDistance a b = 1)
        (blank B₁ :: [c₂, c₃, c₄, c₅]) := by
      rw [hb₁]
      simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
      simp only [gridDistance, c₁, c₂, c₃, c₄, c₅, Nat.dist] at hRH ⊢
      omega
    obtain ⟨B₅, h₅⟩ := Executes.exists_of_chain B₁ _ hchain
    have hb₅ : blank B₅ = c₅ := by rw [h₅.blank_last]; rfl
    have htile : B₅ (R, ⟨w+m+1, by omega⟩) = B (R, ⟨w+m+2, by omega⟩) := by
      rw [h₅.preserves (by
          rw [hb₁]; intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [c₁] at this)
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
            have h1 := congrArg (fun x : Cell n => x.1.val) h <;>
            have h2 := congrArg (fun x : Cell n => x.2.val) h <;>
            simp [c₂, c₃, c₄, c₅] at h1 h2 <;> omega)]
      change swapCells B (blank B) c₁ _ = _
      have : ((R, ⟨w+m+1, by omega⟩) : Cell n) = blank B := by
        rw [hblank]; ext <;> simp <;> omega
      rw [this, swapCells_at_left]
    obtain ⟨C, cs, hC, hlen, hb, htC, hin⟩ := ih B₅ (by omega) (by rw [hb₅])
    refine ⟨C, (c₁ :: [c₂, c₃, c₄, c₅]) ++ cs, (Executes.cons h₁ h₅).append hC,
      by simp [hlen]; ring, hb, ?_, ?_⟩
    · rw [htC, htile]
      congr 3
    · intro x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | hx
      · exact ⟨Or.inl rfl, by dsimp [c₁]; omega, by dsimp [c₁]; omega⟩
      · exact ⟨Or.inr rfl, by dsimp [c₂]; omega, by dsimp [c₂]; omega⟩
      · exact ⟨Or.inr rfl, by dsimp [c₃]; omega, by dsimp [c₃]; omega⟩
      · exact ⟨Or.inr rfl, by dsimp [c₄]; omega, by dsimp [c₄]; omega⟩
      · exact ⟨Or.inl rfl, by dsimp [c₅]; omega, by dsimp [c₅]; omega⟩
      · simp at hx
        have := hin x hx; omega

end
end SlidingPuzzle
