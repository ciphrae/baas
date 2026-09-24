import SlidingPuzzle.Moves.Block
import SlidingPuzzle.Algorithm.PhaseStates

/-! Embedded coordinates for the squares used by Finish. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ}

theorem square_block_end (i : Fin k) : (i.val+1)*k^3 ≤ k^4 := by
  calc
    (i.val+1)*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ i.isLt
    _ = k^4 := by ring

def squareEmbedding (i : GroupIndex k) : Cell (k^3) ↪ Cell (k^4) :=
  blockEmbedding ((groupRow i).val*k^3) ((groupCol i).val*k^3)
    (by simpa [Nat.add_mul] using square_block_end (groupRow i))
    (by simpa [Nat.add_mul] using square_block_end (groupCol i))

theorem mem_range_squareEmbedding (hk : 2 ≤ k) (i : GroupIndex k) (x : Cell (k^4)) :
    x ∈ Set.range (squareEmbedding i) ↔ square i x := by
  let : NeZero (k^3) := ⟨by positivity⟩
  let : NeZero (k^4) := ⟨by positivity⟩
  rw [squareEmbedding,mem_range_blockEmbedding]
  simp [square,Nat.add_mul]

theorem squareEmbedding_mem (hk : 2 ≤ k) (i : GroupIndex k) (c : Cell (k^3)) :
    square i (squareEmbedding i c) :=
  (mem_range_squareEmbedding hk i _).mp ⟨c,rfl⟩

theorem squareEmbedding_target_nonzero [NeZero (k^4)] (hk : 2 ≤ k) (i : GroupIndex k)
    (hi : i ≠ lastGroup k hk) (c : Cell (k^3)) : target (k^4) (squareEmbedding i c) ≠ 0 := by
  intro hz
  have he : squareEmbedding i c=blank (target (k^4)) :=
    (target (k^4)).injective (hz.trans ((target (k^4)).apply_symm_apply 0).symm)
  have hh := squareEmbedding_mem hk i c
  rw [he] at hh
  exact hi ((square_target_blank hk rfl i).mp hh)

/-- Square membership gives the exact local inventory needed by the block solver. -/
theorem squaresSorted_block_labels [NeZero (k^4)] (hk : 2 ≤ k) (B : Board (k^4))
    (hs : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk) :
    ∀ c, ∃ d, B (squareEmbedding i c) = target (k^4) (squareEmbedding i d) := by
  intro c
  have hnonzero : B (squareEmbedding i c) ≠ 0 := by
    intro hz
    have he : squareEmbedding i c=blank B :=
      B.injective (hz.trans (B.apply_symm_apply 0).symm)
    rw [hb] at he
    exact squareEmbedding_target_nonzero hk i hi c (by rw [he]; exact (target _).apply_symm_apply 0)
  have hh := hs i _ (squareEmbedding_mem hk i c) (fun h => hnonzero (Fin.ext h))
  have hpos := (mem_targetGroup i _).mp hh |>.2
  obtain ⟨d,hd⟩ := (mem_range_squareEmbedding hk i _).mpr hpos
  exact ⟨d,by rw [hd]; exact ((target _).apply_symm_apply _).symm⟩
end SlidingPuzzle.Partition
