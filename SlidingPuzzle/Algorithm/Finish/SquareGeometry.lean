import SlidingPuzzle.Moves.Block
import SlidingPuzzle.Algorithm.PhaseStates

/-! Embedded coordinates for the squares used by Finish. -/
namespace SlidingPuzzle.Partition
variable {n k : ℕ}

theorem square_block_end (i : Fin k) : (i.val+1)*side n k ≤ n := by
  calc
    (i.val+1)*side n k ≤ k*side n k := Nat.mul_le_mul_right _ i.isLt
    _ ≤ n := Nat.mul_div_le n k

/-- Square `i` as an embedded board of side `side n k`. -/
def squareEmbedding (i : GroupIndex k) : Cell (side n k) ↪ Cell n :=
  blockEmbedding ((groupRow i).val*side n k) ((groupCol i).val*side n k)
    (by simpa [Nat.add_mul] using square_block_end (groupRow i))
    (by simpa [Nat.add_mul] using square_block_end (groupCol i))

theorem mem_range_squareEmbedding (hk : Dims n k) (i : GroupIndex k) (x : Cell n) :
    x ∈ Set.range (squareEmbedding (n := n) i) ↔ square i x := by
  let : NeZero (side n k) := ⟨hk.side_pos.ne'⟩
  let : NeZero n := ⟨by have := hk.two_le_n; omega⟩
  rw [squareEmbedding,mem_range_blockEmbedding]
  simp [square,Nat.add_mul]

theorem squareEmbedding_mem (hk : Dims n k) (i : GroupIndex k) (c : Cell (side n k)) :
    square i (squareEmbedding (n := n) i c) :=
  (mem_range_squareEmbedding hk i _).mp ⟨c,rfl⟩

theorem squareEmbedding_target_nonzero [NeZero n] (hk : Dims n k) (i : GroupIndex k)
    (hi : i ≠ lastGroup k hk) (c : Cell (side n k)) : target n (squareEmbedding i c) ≠ 0 := by
  intro hz
  have he : squareEmbedding i c=blank (target n) :=
    (target n).injective (hz.trans ((target n).apply_symm_apply 0).symm)
  have hh := squareEmbedding_mem hk i c
  rw [he] at hh
  exact hi ((square_target_blank hk i).mp hh)

/-- Square membership gives the exact local inventory needed by the block solver. -/
theorem squaresSorted_block_labels [NeZero n] (hk : Dims n k) (B : Board n)
    (hs : SquaresSorted (k := k) B) (hb : blank B = blank (target n))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk) :
    ∀ c, ∃ d, B (squareEmbedding i c) = target n (squareEmbedding i d) := by
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
