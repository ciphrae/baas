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
for a vertical strip jump to the chosen row of `H_i`. Both choices stay inside
square `i`. -/
theorem exists_transport_entry_cell {n k : ℕ} (hk : Dims n k) (i : GroupIndex k)
    (low : Bool) (a : Cell n) (ha : reservoir i a) :
    ∃ c : Cell n, horizontal i c ∧
      ((groupCol i).val*side n k ≤ c.2.val ∧ c.2.val < ((groupCol i).val+1)*side n k) ∧
      c.1.val = corridorRow (n := n) i low ∧
      Nat.dist a.2.val c.2.val ≤ 1 ∧ c.2.val ≤ a.2.val ∧
      (a.1.val+a.2.val+c.1.val+c.2.val)%2 = 1 := by
  let r := corridorRow (n := n) i low
  have hgc := (groupCol i).isLt
  have hkk := hk.k_add_two_le
  have hblock := hk.block_le (groupRow i)
  have hrn : r < n := by
    obtain ⟨-, h1, h2⟩ := horizontal_rows hk i
    cases low
    · exact h1
    · exact h2
  have hk2 : 1 ≤ k^2 := by have := pow_pos (by omega : 0 < k) 2; omega
  have hcol : 1 ≤ a.2.val := by have := ha.2.2.1; omega
  let d := if (a.1.val+a.2.val+r+a.2.val)%2 = 1 then 0 else 1
  have hd : d ≤ 1 := by dsimp [d]; split_ifs <;> omega
  let c : Cell n := (⟨r, hrn⟩, ⟨a.2.val-d, by omega⟩)
  refine ⟨c, horizontal_of_corridorRow low rfl, ?_, rfl, ?_, by dsimp [c]; omega, ?_⟩
  · have hclo := ha.2.2.1
    have hchi := ha.2.2.2
    exact ⟨by change _ ≤ a.2.val-d; omega, by change a.2.val-d < _; omega⟩
  · dsimp [c, Nat.dist]; omega
  · dsimp [c, d]; split_ifs <;> omega

/-- A legal entry jump to the chosen row of `H_i`, with exact two-cell effect.
The jump restores every other cell, so it is charged at half its length. Its
cost depends only on the blank's row distance to that row. -/
theorem exists_transport_entry_path {n k : ℕ} [NeZero n]
    (hk : Dims n k) (hn : 2 ≤ n) (B : Board n) (hB : Clear (k := k) B)
    (i : GroupIndex k) (low : Bool) (hi : reservoir i (blank B)) :
    ∃ D : Board n, ∃ p : Path B D,
      horizontal i (blank D) ∧
      ((groupCol i).val*side n k ≤ (blank D).2.val ∧
        (blank D).2.val < ((groupCol i).val+1)*side n k) ∧
      (blank D).1.val = corridorRow (n := n) i low ∧
      Nat.dist (blank B).2.val (blank D).2.val ≤ 1 ∧ (blank D).2.val ≤ (blank B).2.val ∧
      GroupEquivalent i B D ∧
      2*p.inefficientMoves ≤ 26*(Nat.dist (blank B).1.val (corridorRow (n := n) i low)+1) := by
  obtain ⟨c, hcH, hcS, hcr, hcD, hcle, hcP⟩ := exists_transport_entry_cell hk i low (blank B) hi
  obtain ⟨p, hp⟩ := exists_vertical_jump hn B c hcD hcP
  refine ⟨swapCells B (blank B) c, p, ?_, ?_, by simpa using hcr, by simpa using hcD,
    by simpa using hcle, ?_, ?_⟩
  · simpa using hcH
  · simpa using hcS
  · exact groupEquivalent_swap hk B i c (hB.1 i c hcH)
  · have hhalf := p.two_inefficientMoves_le_of_blank_swap
    have hd : gridDistance (blank B) c ≤
        Nat.dist (blank B).1.val (corridorRow (n := n) i low)+1 := by
      simp only [gridDistance, ← hcr]
      omega
    rw [← hcr] at hd ⊢
    omega

/-- Entry and horizontal travel. The endpoint is in the chosen row of `H_i` at
any requested column and retains the filled-blank group invariant relative to
the original clear board. The entry jump's cost depends on the blank's row
distance. -/
theorem exists_transport_horizontal_path {n k : ℕ} [NeZero n]
    (hk : Dims n k) (hn : 2 ≤ n) (B : Board n) (hB : Clear (k := k) B)
    (i : GroupIndex k) (low : Bool) (hi : reservoir i (blank B)) (column : Fin n) :
    ∃ D : Board n, ∃ p : Path B D,
      horizontal i (blank D) ∧ (blank D).1.val = corridorRow (n := n) i low ∧
      (blank D).2 = column ∧
      GroupEquivalent i B D ∧ 2*p.inefficientMoves ≤
        2*side n k+26*(Nat.dist (blank B).1.val (corridorRow (n := n) i low)+1) ∧
      ((blank B).2.val ≤ column.val → 2*p.inefficientMoves ≤
        2*((groupCol i).val*side n k+side n k+1-(blank B).2.val)+
          26*(Nat.dist (blank B).1.val (corridorRow (n := n) i low)+1)) ∧
      (column.val < (blank B).2.val → 2*p.inefficientMoves ≤
        2*((blank B).2.val+1-(groupCol i).val*side n k)+
          26*(Nat.dist (blank B).1.val (corridorRow (n := n) i low)+1)) := by
  obtain ⟨D, p, hDH, hDS, hDr, hcD, hcle, hBD, hp⟩ :=
    exists_transport_entry_path hk hn B hB i low hi
  have hg : ∀ c : Cell n, c.1 = (blank D).1 → c ≠ blank D → D c ∈ targetGroup i := by
    intro c hc hne
    apply hBD.mem_targetGroup _ hne
    apply hB.1 i c
    exact horizontal_of_corridorRow low (by rw [hc]; exact hDr)
  obtain ⟨F, q, hblank, hq, hqr, hql, hqleft, hgroup, hfix⟩ :=
    exists_horizontal_transport_slide_dir' i D (blank D).1 (blank D).2 column rfl hDS hg
  have hDF : GroupEquivalent i D F := by
    apply groupEquivalent_of_region hk i D F {c | c.1 = (blank D).1} rfl
      (by change (blank F).1 = _; rw [hblank])
    · exact hg
    · exact hgroup
    · exact hfix
  have hFr : (blank F).1.val = corridorRow (n := n) i low := by rw [hblank]; exact hDr
  refine ⟨F, p.append q, horizontal_of_corridorRow low hFr, hFr, ?_, hBD.trans hDF, ?_, ?_, ?_⟩
  · rw [hblank]
  · rw [Path.inefficientMoves_append]
    omega
  · intro hc
    rw [Path.inefficientMoves_append]
    have h1 := hqr (by change (blank D).2.val ≤ column.val; omega)
    simp only [Nat.dist] at hcD
    omega
  · intro hc
    rw [Path.inefficientMoves_append]
    by_cases hce : (blank D).2 ≤ column
    · have h2 := hql hce
      change (blank D).2.val ≤ column.val at hce
      simp only [Nat.dist] at hcD
      omega
    · have h3 := hqleft (not_le.mp hce)
      omega

end
end SlidingPuzzle.Partition
