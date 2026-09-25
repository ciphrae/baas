import SlidingPuzzle.Moves.Corridor
import SlidingPuzzle.Algorithm.Partition
import SlidingPuzzle.Algorithm.Accounting

/-! The straight-corridor estimate in Algorithm 4, Fact 3: a slide of tiles
from group `i`, starting in square `i`, has at most `k³` inefficient moves. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- Horizontal and vertical slides of a single target group cost at most one
block width in inefficient moves. Reversing the line handles left/up motion.
The board may have a blank in the corridor, as it does during transport. -/
theorem exists_group_corridor_path {n k : ℕ} [NeZero n]
    (i : GroupIndex k) (vertical backwards : Bool) (fixed a b : Fin n)
    (hab : a ≤ b) (B : Board n)
    (hblank : blank B = corridorCell vertical backwards fixed a)
    (hstart : square i (blank B))
    (hgroup : ∀ x : Fin n, a ≤ x → x ≤ b → x ≠ a →
      B (corridorCell vertical backwards fixed x) ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = corridorCell vertical backwards fixed b ∧ p.length = b.val - a.val ∧
      p.inefficientMoves ≤ side n k ∧
      p.inefficientMoves ≤ (if backwards then n - (if vertical then (groupRow i).val * side n k
        else (groupCol i).val * side n k) else (if vertical then (groupRow i).val * side n k
        else (groupCol i).val * side n k) + side n k) - a.val ∧
      (∀ x : Fin n, a ≤ x → x ≤ b → x ≠ b →
        C (corridorCell vertical backwards fixed x) ∈ targetGroup i) ∧
      (∀ c : Cell n, (∀ x : Fin n, a ≤ x → x ≤ b →
        c ≠ corridorCell vertical backwards fixed x) → C c = B c) := by
  let lo := if vertical then (groupRow i).val * side n k else (groupCol i).val * side n k
  have ht : ∀ t ∈ (targetGroup (n := n) i : Set (Tile n)),
      lo ≤ corridorCoordinate vertical (position (target n) t) ∧
        corridorCoordinate vertical (position (target n) t) < lo + side n k := by
    intro t ht
    have hs := (mem_targetGroup i t).mp ht |>.2
    cases vertical <;> simp only [lo, corridorCoordinate, Bool.false_eq_true, ↓reduceIte]
    · exact ⟨hs.2.2.1, by have := hs.2.2.2; nlinarith⟩
    · exact ⟨hs.1, by have := hs.2.1; nlinarith⟩
  have hs : lo ≤ corridorCoordinate vertical (corridorCell vertical backwards fixed a) ∧
      corridorCoordinate vertical (corridorCell vertical backwards fixed a) < lo + side n k := by
    rw [← hblank]
    cases vertical <;> simp only [lo, corridorCoordinate, Bool.false_eq_true, ↓reduceIte]
    · exact ⟨hstart.2.2.1, by have := hstart.2.2.2; nlinarith⟩
    · exact ⟨hstart.1, by have := hstart.2.1; nlinarith⟩
  simpa only [Nat.add_sub_cancel_left, Finset.mem_coe] using
    exists_oriented_corridor_path vertical backwards fixed a b hab
      (targetGroup (n := n) i : Set (Tile n)) lo (lo + side n k) ht hs B hblank hgroup

private theorem exists_horizontal_group_slide_oriented {n k : ℕ} [NeZero n]
    (i : GroupIndex k) (backwards : Bool) (r a b : Fin n) (hab : a ≤ b)
    (B : Board n) (hb : blank B = corridorCell false backwards r a)
    (hs : square i (blank B))
    (hg : ∀ c : Cell n, c.1 = r → c ≠ blank B → B c ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = corridorCell false backwards r b ∧ p.inefficientMoves ≤ side n k ∧
      p.inefficientMoves ≤ (if backwards then n - (groupCol i).val * side n k
        else (groupCol i).val * side n k + side n k) - a.val ∧
      p.inefficientMoves ≤ b.val - a.val ∧
      (∀ c : Cell n, c.1 = r → c ≠ blank C → C c ∈ targetGroup i) ∧
      (∀ c : Cell n, c.1 ≠ r → C c = B c) := by
  let line := corridorCell false backwards r
  have hinj : Function.Injective line := by
    intro x y h
    cases backwards <;> simpa [line, corridorCell] using h
  obtain ⟨C, p, hc, hp, he, hdir, hseg, hfix⟩ :=
    exists_group_corridor_path i false backwards r a b hab B hb hs (by
      intro x _ _ hxa
      apply hg _ (by simp [corridorCell])
      rw [hb]
      exact fun h => hxa (hinj h))
  refine ⟨C, p, hc, he, by simpa using hdir, hp ▸ p.inefficientMoves_le_length, ?_, ?_⟩
  · intro c hrow hne
    let x := if backwards then c.2.rev else c.2
    have hcell : line x = c := by
      cases backwards <;> simp [line, corridorCell, x, ← hrow]
    have hxb : x ≠ b := by
      intro h
      apply hne
      rw [← hcell, h]
      exact hc.symm
    by_cases hx : a ≤ x ∧ x ≤ b
    · rw [← hcell]
      exact hseg x hx.1 hx.2 hxb
    · rw [hfix c (by
        intro y hay hyb hcy
        have heq : x = y := hinj (hcell.trans hcy)
        exact hx (heq ▸ ⟨hay, hyb⟩))]
      apply hg c hrow
      intro hcb
      have heq : x = a := hinj (hcell.trans (hcb.trans hb))
      apply hx
      rw [heq]
      exact ⟨le_rfl, hab⟩
  · intro c hrow
    apply hfix c
    intro x _ _ hcx
    exact hrow (by simpa [corridorCell] using congrArg Prod.fst hcx)

/-- The horizontal slide with a start-dependent bound: moving right from column
`a` costs at most the distance to the square's right edge, moving left at most
one more than the distance to its left edge. -/
theorem exists_horizontal_transport_slide_dir' {n k : ℕ} [NeZero n]
    (i : GroupIndex k) (B : Board n) (r a b : Fin n)
    (hb : blank B = (r, a)) (hs : square i (blank B))
    (hg : ∀ c : Cell n, c.1 = r → c ≠ blank B → B c ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = (r, b) ∧ p.inefficientMoves ≤ side n k ∧
      (a ≤ b → p.inefficientMoves ≤ (groupCol i).val * side n k + side n k - a.val) ∧
      (a ≤ b → p.inefficientMoves ≤ b.val - a.val) ∧
      (b < a → p.inefficientMoves ≤ a.val + 1 - (groupCol i).val * side n k) ∧
      (∀ c : Cell n, c.1 = r → c ≠ blank C → C c ∈ targetGroup i) ∧
      (∀ c : Cell n, c.1 ≠ r → C c = B c) := by
  by_cases hab : a ≤ b
  · obtain ⟨C, p, hc, he, hdir, hlen, hg', hf⟩ := exists_horizontal_group_slide_oriented i false r
      a b hab B (by simpa [corridorCell] using hb) hs hg
    refine ⟨C, p, by simpa [corridorCell] using hc, he, fun _ => by simpa using hdir,
      fun _ => hlen, fun h => absurd hab (not_le.mpr h), hg', hf⟩
  · have hrev : a.rev ≤ b.rev := by simp only [Fin.le_def, Fin.rev]; omega
    obtain ⟨C, p, hc, he, hdir, -, hg', hf⟩ := exists_horizontal_group_slide_oriented i true r
      a.rev b.rev hrev B (by simpa [corridorCell] using hb) hs hg
    refine ⟨C, p, by simpa [corridorCell] using hc, he, fun h => absurd h hab,
      fun h => absurd h hab, fun _ => ?_, hg', hf⟩
    simp only [↓reduceIte, Fin.val_rev] at hdir
    have := a.isLt
    omega


/-- Algorithm 4's horizontal slide (step (ii)), after the blank has entered
`H_i`. It can go to any column, preserves the corridor's group membership
except at the new blank, fixes all other rows, and costs at most `k³`
inefficient moves. No `Clear` assumption is imposed while the blank is in H_i. -/
theorem exists_horizontal_transport_slide {n k : ℕ} [NeZero n]
    (i : GroupIndex k) (B : Board n) (r a b : Fin n)
    (hb : blank B = (r, a)) (hs : square i (blank B))
    (hg : ∀ c : Cell n, c.1 = r → c ≠ blank B → B c ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = (r, b) ∧ p.inefficientMoves ≤ side n k ∧
      (∀ c : Cell n, c.1 = r → c ≠ blank C → C c ∈ targetGroup i) ∧
      (∀ c : Cell n, c.1 ≠ r → C c = B c) := by
  obtain ⟨C, p, hc, he, -, -, -, hg', hf⟩ := exists_horizontal_transport_slide_dir' i B r a b hb hs hg
  exact ⟨C, p, hc, he, hg', hf⟩

end
end SlidingPuzzle.Partition
