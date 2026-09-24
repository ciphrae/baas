import SlidingPuzzle.Moves.Relabel

/-! Cubic local solving without assuming the local parity condition. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Exchanging two labels is the same board operation as exchanging their cells. -/
theorem relabel_swap (B : Board n) (a b : Tile n) :
    relabel B (Equiv.swap a b) = swapCells B (B.symm a) (B.symm b) := by
  have h := Equiv.trans_swap_trans_symm a b B
  have hh := congrArg (fun e => e.trans B) h
  simpa [relabel,swapCells,Equiv.trans_assoc] using hh

omit [NeZero n] in
/-- A finite embedded set of labels determines an actual local board. -/
theorem exists_board_of_embedded_labels {m : ℕ} (ι : Cell m ↪ Cell n)
    (η : Tile m ↪ Tile n) (B : Board n)
    (hlabels : ∀ c, B (ι c) ∈ Set.range η) :
    ∃ A : Board m, ∀ c, B (ι c) = η (A c) := by
  classical
  choose f hf using hlabels
  have hinj : Function.Injective f := by
    intro a b h
    exact ι.injective (B.injective (by rw [← hf a,← hf b,h]))
  have hcard : Fintype.card (Cell m) = Fintype.card (Tile m) := by simp
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩
  exact ⟨Equiv.ofBijective f hsurj,fun c => (hf c).symm⟩
end SlidingPuzzle
