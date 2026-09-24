import SlidingPuzzle.Algorithm.TransportCorridors
import SlidingPuzzle.Algorithm.TransportLabels

/-! Vertical corridor segments with a remaining-distance budget. Segments
outside the destination row band are efficient when moving away from it;
they must not each be charged an independent k³ allowance. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- A legal corridor route retains the filled-blank group invariant. -/
theorem exists_group_corridor_route {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (i : GroupIndex k) (line : Fin n → Cell n)
    (hinj : Function.Injective line)
    (hadj : ∀ x y : Fin n, x.val+1 = y.val → gridDistance (line x) (line y) = 1)
    (cap : ℕ)
    (hefficient : ∀ (x y : Fin n) (t : Tile n), x.val+1 = y.val → cap ≤ x.val →
      t ∈ targetGroup i → gridDistance (line x) (position (target n) t)+1 =
        gridDistance (line y) (position (target n) t))
    (a b : Fin n) (hab : a ≤ b) (B : Board n) (hb : blank B = line a)
    (hg : ∀ x : Fin n, a ≤ x → x ≤ b → x ≠ a → B (line x) ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = line b ∧ GroupEquivalent i B C ∧ p.inefficientMoves ≤ cap-a.val := by
  obtain ⟨C, p, hC, _hp, he, hgroup, hfix⟩ := exists_increasing_corridor_path
    line hinj hadj (targetGroup (n := n) i : Set (Tile n)) cap hefficient a b hab B hb hg
  refine ⟨C, p, hC, ?_, he⟩
  let S : Set (Cell n) := {c | ∃ x : Fin n, a ≤ x ∧ x ≤ b ∧ line x = c}
  apply groupEquivalent_of_region hk i B C S
    ⟨a, le_rfl, hab, hb.symm⟩ ⟨b, hab, le_rfl, hC.symm⟩
  · rintro c ⟨x, hax, hxb, rfl⟩ hne
    exact hg x hax hxb (fun h => hne (h ▸ hb.symm))
  · rintro c ⟨x, hax, hxb, rfl⟩ hne
    exact hgroup x hax hxb (fun h => hne (h ▸ hC.symm))
  · intro c hc
    apply hfix c
    intro x hax hxb hcx
    exact hc ⟨x, hax, hxb, hcx.symm⟩

/-- Move through a single vertical corridor, retaining the group invariant.
Ranks increase in the chosen direction (`backwards` means upward). The bound
is the distance to the destination band's threshold, truncated at zero. -/
theorem exists_vertical_corridor_segment {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (A B : Board n) (hA : Clear (k := k) A)
    (i j : GroupIndex k) (hAB : GroupEquivalent i A B)
    (backwards : Bool) (column a b : Fin n) (hab : a ≤ b)
    (hblank : blank B = corridorCell true backwards column a)
    (ha : vertical j i (corridorCell true backwards column a))
    (hb : vertical j i (corridorCell true backwards column b)) :
    ∃ D : Board n, ∃ p : Path B D,
      blank D = corridorCell true backwards column b ∧ GroupEquivalent i A D ∧
      p.inefficientMoves ≤
        (if backwards then n-(groupRow i).val*k^3 else ((groupRow i).val+1)*k^3)-a.val := by
  let line := corridorCell true backwards column
  let cap := if backwards then n-(groupRow i).val*k^3 else ((groupRow i).val+1)*k^3
  have hinj : Function.Injective line := by
    intro x y h
    cases backwards <;> simpa [line, corridorCell] using h
  have hadj : ∀ x y : Fin n, x.val+1 = y.val → gridDistance (line x) (line y) = 1 := by
    intro x y h
    cases backwards <;> simp [line, corridorCell, gridDistance, Fin.rev, Nat.dist] <;> omega
  have hefficient : ∀ (x y : Fin n) (t : Tile n), x.val+1 = y.val → cap ≤ x.val →
      t ∈ targetGroup i → gridDistance (line x) (position (target n) t)+1 =
        gridDistance (line y) (position (target n) t) := by
    intro x y t hxy hcap ht
    have hsq := (mem_targetGroup i t).mp ht |>.2
    have hlo := hsq.1
    have hhi := hsq.2.1
    cases backwards <;>
      simp only [line, cap, corridorCell, Bool.false_eq_true, ↓reduceIte,
        gridDistance, Fin.rev, Nat.dist] at hcap ⊢ <;> omega
  have hg : ∀ x : Fin n, a ≤ x → x ≤ b → x ≠ a → B (line x) ∈ targetGroup i := by
    intro x hax hxb hxa
    apply hAB.mem_targetGroup _ (by rw [hblank]; exact fun h => hxa (hinj h))
    apply hA.2 j i
    have hcol : (line x).2.val = (groupCol j).val*k^3+i.val := by
      simpa [line, corridorCell] using ha.2.2
    refine ⟨?_, ?_, hcol⟩ <;>
      cases backwards <;>
      simp only [line, corridorCell, ↓reduceIte, Bool.false_eq_true, Fin.rev, vertical] at ha hb ⊢ <;>
      omega
  obtain ⟨D, p, hD, hBD, hp⟩ := exists_group_corridor_route hk i line hinj hadj cap
    hefficient a b hab B hblank hg
  exact ⟨D, p, hD, hAB.trans hBD, hp⟩

end
end SlidingPuzzle.Partition
