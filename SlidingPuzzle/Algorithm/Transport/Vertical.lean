import SlidingPuzzle.Moves.Corridor
import SlidingPuzzle.Algorithm.Transport.Labels

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

end
end SlidingPuzzle.Partition
