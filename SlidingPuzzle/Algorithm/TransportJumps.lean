import SlidingPuzzle.Moves.Jump
import SlidingPuzzle.Algorithm.TransportLabels

/-! Parity-adjusted vertical jumps for crossing the horizontal corridor bands.
All displaced nonblank tiles stay in the same target group. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- A neighboring group-i buffer resolves either parity when jumping along a
column. The endpoint is the requested cell, all other group memberships are
preserved, and the cost is linear in the vertical gap. -/
theorem exists_group_vertical_jump {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hn : 2 ≤ n) (B : Board n) (i : GroupIndex k)
    (b u : Cell n) (hb : B b ∈ targetGroup i) (hu : B u ∈ targetGroup i)
    (hbc : b.2 = (blank B).2)
    (hadj : gridDistance (blank B) u = 1) :
    ∃ D : Board n, ∃ p : Path B D,
      blank D = b ∧ GroupEquivalent i B D ∧
      p.length ≤ 26*(Nat.dist (blank B).1.val b.1.val+2) := by
  have hbne : b ≠ blank B := by
    intro h
    have hz : B (blank B) = 0 := B.apply_symm_apply 0
    rw [h, hz] at hb
    exact zero_not_mem_targetGroup i hb
  by_cases hpar : ((blank B).1.val+(blank B).2.val+b.1.val+b.2.val)%2 = 1
  · obtain ⟨p, hp⟩ := exists_vertical_jump hn B b (by simp [hbc]) hpar
    refine ⟨swapCells B (blank B) b, p, blank_swapCells B b,
      groupEquivalent_swap hk B i b hb, ?_⟩
    omega
  · have hbu : b ≠ u := by
      intro h
      subst b
      simp only [gridDistance, Nat.dist] at hadj
      omega
    let C := swapCells B (blank B) u
    let p := movePath B u hadj
    have hCb : C b ∈ targetGroup i := by
      change swapCells B (blank B) u b ∈ _
      rw [swapCells_preserves B hbne hbu]
      exact hb
    have hcolor : ((blank C).1.val+(blank C).2.val+b.1.val+b.2.val)%2 = 1 := by
      dsimp [C]
      rw [blank_swapCells]
      simp only [gridDistance, Nat.dist] at hadj
      omega
    obtain ⟨q, hq⟩ := exists_vertical_jump hn C b (by
      simp only [C, blank_swapCells]
      have hc := congrArg Fin.val hbc
      simp only [gridDistance, Nat.dist] at hadj
      simp only [Nat.dist]; omega) hcolor
    refine ⟨swapCells C (blank C) b, p.append q, blank_swapCells C b,
      (groupEquivalent_swap hk B i u hu).trans (groupEquivalent_swap hk C i b hCb), ?_⟩
    have hgap : Nat.dist u.1.val b.1.val ≤ Nat.dist (blank B).1.val b.1.val + 1 := by
      simp only [gridDistance, Nat.dist] at hadj
      simp only [Nat.dist]
      omega
    simp only [C, blank_swapCells] at hq
    rw [Path.length_append]
    have hp : p.length = 1 := rfl
    omega

end
end SlidingPuzzle.Partition
