import SlidingPuzzle.Algorithm.Accounting
import SlidingPuzzle.Algorithm.Transport.Corridors
import SlidingPuzzle.Algorithm.Transport.Labels
import SlidingPuzzle.Moves.Jump

/-! Enter the horizontal corridor from the blank's reservoir, then slide to
the selected vertical corridor. These are steps (i) and (ii) of Algorithm 4. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- One of the blank's column and its preceding column has the right parity
for a vertical strip jump to H_i. Both choices stay inside square i. -/
theorem exists_transport_entry_cell {n k : ℕ} (hk : Dims n k) (i : GroupIndex k)
    (a : Cell n) (ha : reservoir i a) :
    ∃ c : Cell n, horizontal i c ∧ square i c ∧
      Nat.dist a.2.val c.2.val ≤ 1 ∧
      (a.1.val+a.2.val+c.1.val+c.2.val)%2 = 1 ∧
      Nat.dist a.1.val c.1.val + 1 ≤ side n k := by
  let r := (groupRow i).val*side n k + (groupCol i).val
  have hrow : r < a.1.val := by
    have hgc := (groupCol i).isLt
    have := ha.1
    dsimp [r]; omega
  have hk2 : 1 ≤ k^2 := by have := pow_pos (by omega : 0 < k) 2; omega
  have hcol : 1 ≤ a.2.val := by have := ha.2.2.1; omega
  let d := if (a.1.val+a.2.val+r+a.2.val)%2 = 1 then 0 else 1
  have hd : d ≤ 1 := by dsimp [d]; split_ifs <;> omega
  let c : Cell n := (⟨r, hrow.trans a.1.isLt⟩, ⟨a.2.val-d, by omega⟩)
  refine ⟨c, rfl, ?_, ?_, ?_, ?_⟩
  · have hrlo : (groupRow i).val*side n k ≤ r := by dsimp [r]; omega
    have hrhi := ha.2.1
    have hclo := ha.2.2.1
    have hchi := ha.2.2.2
    exact ⟨hrlo, by change r < _; omega, by change _ ≤ a.2.val-d; omega,
      by change a.2.val-d < _; omega⟩
  · dsimp [c, Nat.dist]; omega
  · dsimp [c, d]; split_ifs <;> omega
  · have hrlo : (groupRow i).val*side n k ≤ r := by dsimp [r]; omega
    have hrhi := ha.2.1
    simp only [Nat.add_mul, Nat.one_mul] at hrhi
    dsimp [c, Nat.dist]; omega

/-- A legal entry jump, with exact two-cell effect. The jump restores every
other cell, so it is charged at half its length. Its cost depends only on the
blank's row distance to H_i. -/
theorem exists_transport_entry_path {n k : ℕ} [NeZero n]
    (hk : Dims n k) (hn : 2 ≤ n) (B : Board n) (hB : Clear (k := k) B)
    (i : GroupIndex k) (hi : reservoir i (blank B)) :
    ∃ D : Board n, ∃ p : Path B D,
      horizontal i (blank D) ∧ square i (blank D) ∧
      GroupEquivalent i B D ∧
      2*p.inefficientMoves ≤ 26*((blank B).1.val-((groupRow i).val*side n k+(groupCol i).val)+1) := by
  obtain ⟨c, hcH, hcS, hcD, hcP, _⟩ := exists_transport_entry_cell hk i (blank B) hi
  obtain ⟨p, hp⟩ := exists_vertical_jump hn B c hcD hcP
  refine ⟨swapCells B (blank B) c, p, ?_, ?_, ?_, ?_⟩
  · simpa using hcH
  · simpa using hcS
  · exact groupEquivalent_swap hk B i c (hB.1 i c hcH)
  · have hhalf := p.two_inefficientMoves_le_of_blank_swap
    have hrow : c.1.val = (groupRow i).val*side n k+(groupCol i).val := hcH
    have hlo : (groupRow i).val*side n k+(groupCol i).val < (blank B).1.val := by
      have := hi.1; have := (groupCol i).isLt; omega
    have hdist : Nat.dist (blank B).1.val c.1.val =
        (blank B).1.val-((groupRow i).val*side n k+(groupCol i).val) := by
      simp only [Nat.dist]; omega
    have hd : gridDistance (blank B) c ≤
        (blank B).1.val-((groupRow i).val*side n k+(groupCol i).val)+1 := by
      simp only [gridDistance]
      omega
    rw [hdist] at hp
    omega

/-- Entry and horizontal travel. The endpoint is in H_i at any requested
column and retains the filled-blank group invariant relative to the original
clear board. The entry jump's cost depends on the blank's row distance. -/
theorem exists_transport_horizontal_path {n k : ℕ} [NeZero n]
    (hk : Dims n k) (hn : 2 ≤ n) (B : Board n) (hB : Clear (k := k) B)
    (i : GroupIndex k) (hi : reservoir i (blank B)) (column : Fin n) :
    ∃ D : Board n, ∃ p : Path B D,
      horizontal i (blank D) ∧ (blank D).2 = column ∧
      GroupEquivalent i B D ∧ 2*p.inefficientMoves ≤
        2*side n k+26*((blank B).1.val-((groupRow i).val*side n k+(groupCol i).val)+1) := by
  obtain ⟨D, p, hDH, hDS, hBD, hp⟩ := exists_transport_entry_path hk hn B hB i hi
  have hg : ∀ c : Cell n, c.1 = (blank D).1 → c ≠ blank D → D c ∈ targetGroup i := by
    intro c hc hne
    apply hBD.mem_targetGroup _ hne
    apply hB.1 i c
    change c.1.val = _
    rw [hc]
    exact hDH
  obtain ⟨F, q, hblank, hq, hgroup, hfix⟩ := exists_horizontal_transport_slide i D
    (blank D).1 (blank D).2 column rfl hDS hg
  have hDF : GroupEquivalent i D F := by
    apply groupEquivalent_of_region hk i D F {c | c.1 = (blank D).1} rfl
      (by change (blank F).1 = _; rw [hblank])
    · exact hg
    · exact hgroup
    · exact hfix
  refine ⟨F, p.append q, ?_, ?_, hBD.trans hDF, ?_⟩
  · change (blank F).1.val = _
    rw [hblank]
    exact hDH
  · rw [hblank]
  · rw [Path.inefficientMoves_append]
    omega

end
end SlidingPuzzle.Partition
