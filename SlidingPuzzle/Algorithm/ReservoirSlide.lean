import SlidingPuzzle.Algorithm.TransportLabels
import SlidingPuzzle.Algorithm.CountSwap

/-! Moves inside one reservoir. Transport only needs reservoir counts and clear
corridors, so the blank may rearrange its own reservoir freely. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- Exchanging two cells of the same reservoir leaves every count unchanged. -/
theorem boardMatrix_swap_same_reservoir {n k : ℕ} (hk : 2 ≤ k) (B : Board n)
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

/-- Slide the blank up its column to the first row of its reservoir. Counts
and clear corridors are preserved; only reservoir cells move. -/
theorem exists_reservoir_top_path {n k : ℕ} [NeZero n] (hk : 2 ≤ k)
    (B : Board n) (hB : Clear (k := k) B) (i : GroupIndex k)
    (hi : reservoir i (blank B)) :
    ∃ C : Board n, ∃ p : Path B C,
      Clear (k := k) C ∧ reservoir i (blank C) ∧
      (blank C).1.val = (groupRow i).val*k^3+k ∧ (blank C).2 = (blank B).2 ∧
      boardMatrix hk C = boardMatrix hk B ∧
      p.length + ((groupRow i).val*k^3+k) = (blank B).1.val := by
  generalize hm : (blank B).1.val - ((groupRow i).val*k^3+k) = m
  induction m generalizing B with
  | zero =>
    have hlo := hi.1
    exact ⟨B, .nil B, hB, hi, by omega, rfl, rfl, by simp; omega⟩
  | succ m ih =>
    let a := blank B
    have hlo := hi.1
    let c : Cell n := (⟨a.1.val-1, by have := a.1.isLt; omega⟩, a.2)
    have hc : reservoir i c := ⟨by dsimp [c, a]; omega,
      by have := hi.2.1; dsimp [c, a]; omega, hi.2.2.1, hi.2.2.2⟩
    have hd : gridDistance (blank B) c = 1 := by
      simp only [gridDistance, c, a, Nat.dist]; omega
    have hne : blank B ≠ c := by
      intro h
      have := congrArg (fun x : Cell n => x.1.val) h
      dsimp [c, a] at this; omega
    let B' := swapCells B (blank B) c
    have hB' : Clear (k := k) B' := clear_swap_reservoirs hk B hB hi hc
    have hb' : blank B' = c := blank_swapCells B c
    obtain ⟨C, p, hC, hCi, hrow, hcol, hmat, hlen⟩ :=
      ih B' hB' (by rw [hb']; exact hc) (by rw [hb']; dsimp [c, a]; omega)
    refine ⟨C, (movePath B c hd).append p, hC, hCi, hrow, ?_, ?_, ?_⟩
    · rw [hcol, hb']
    · rw [hmat]
      exact boardMatrix_swap_same_reservoir hk B hi hc hne
    · rw [Path.length_append, movePath_length]
      rw [hb'] at hlen
      dsimp [c, a] at hlen
      omega

end
end SlidingPuzzle.Partition
