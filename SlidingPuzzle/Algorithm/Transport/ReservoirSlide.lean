import SlidingPuzzle.Algorithm.Transport.BoardMatrix

/-! Moves inside one reservoir. Transport only needs reservoir counts and clear
corridors, so the blank may rearrange its own reservoir freely. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- Exchanging two cells of the same reservoir leaves every count unchanged. -/
theorem boardMatrix_swap_same_reservoir {n k : ℕ} (hk : Dims n k) (B : Board n)
    {a c : Cell n} {i : GroupIndex k} (ha : reservoir i a) (hc : reservoir i c)
    (hac : a ≠ c) : boardMatrix hk (swapCells B a c) = boardMatrix hk B := by
  funext r s
  have h := reservoirCount_swap_balance B a c hac (transportIndex k hk r) (transportIndex k hk s)
  unfold boardMatrix
  by_cases hr : reservoir (transportIndex k hk r) a
  · have hr' : reservoir (transportIndex k hk r) c := reservoir_unique hk hr ha ▸ hc
    simp only [hr, hr', true_and] at h
    split_ifs at h <;> omega
  · have hr' : ¬ reservoir (transportIndex k hk r) c :=
      fun h => hr (reservoir_unique hk h hc ▸ ha)
    simp only [hr, hr', false_and, ↓reduceIte] at h
    omega

/-- Slide the blank along its column to any row `y` of its reservoir. Counts,
clear corridors and every cell outside the reservoir are preserved. -/
theorem exists_reservoir_slide_path {n k : ℕ} [NeZero n] (hk : Dims n k)
    (B : Board n) (hB : Clear (k := k) B) (i : GroupIndex k)
    (hi : reservoir i (blank B)) (y : ℕ) (hy : (groupRow i).val*side n k+2*k ≤ y)
    (hy' : y < ((groupRow i).val+1)*side n k) :
    ∃ C : Board n, ∃ p : Path B C,
      Clear (k := k) C ∧ reservoir i (blank C) ∧
      (blank C).1.val = y ∧ (blank C).2 = (blank B).2 ∧
      boardMatrix hk C = boardMatrix hk B ∧
      p.length = Nat.dist (blank B).1.val y ∧
      ∀ x : Cell n, ¬ reservoir i x → C x = B x := by
  generalize hm : Nat.dist (blank B).1.val y = m
  induction m generalizing B with
  | zero =>
    refine ⟨B, .nil B, hB, hi, ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
    simp only [Nat.dist] at hm; omega
  | succ m ih =>
    have hlo := hi.1
    have hhi := hi.2.1
    let r : ℕ := if y < (blank B).1.val then (blank B).1.val-1 else (blank B).1.val+1
    have hr : (groupRow i).val*side n k+2*k ≤ r ∧ r < ((groupRow i).val+1)*side n k := by
      simp only [Nat.dist] at hm; dsimp [r]; split_ifs <;> omega
    let c : Cell n := (⟨r, by have := hr.2; have := hk.block_le (groupRow i); omega⟩, (blank B).2)
    have hc : reservoir i c := ⟨hr.1, hr.2, hi.2.2.1, hi.2.2.2⟩
    have hd : gridDistance (blank B) c = 1 := by
      simp only [Nat.dist] at hm
      simp only [gridDistance, c, r, Nat.dist]; split_ifs <;> omega
    have hne : blank B ≠ c := by
      intro h; rw [h, gridDistance_self] at hd; omega
    let B' := swapCells B (blank B) c
    have hB' : Clear (k := k) B' := clear_swap_reservoirs hk B hB hi hc
    have hb' : blank B' = c := blank_swapCells B c
    obtain ⟨C, p, hC, hCi, hrow, hcol, hmat, hlen, hfix⟩ :=
      ih B' hB' (by rw [hb']; exact hc) (by
        rw [hb']; simp only [Nat.dist] at hm ⊢; dsimp [c, r]; split_ifs <;> omega)
    refine ⟨C, (movePath B c hd).append p, hC, hCi, hrow, ?_, ?_, ?_, ?_⟩
    · rw [hcol, hb']
    · rw [hmat]
      exact boardMatrix_swap_same_reservoir hk B hi hc hne
    · rw [Path.length_append, movePath_length, hlen]
      omega
    · intro x hx
      rw [hfix x hx]
      exact swapCells_preserves B (fun h => hx (h ▸ hi)) (fun h => hx (h ▸ hc))

end
end SlidingPuzzle.Partition
