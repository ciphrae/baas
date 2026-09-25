import SlidingPuzzle.Manhattan
import SlidingPuzzle.Moves.Local

/-! Monotone corridor slides with an inefficient-move budget. Unlike a bound
on total length, the budget can be independent of the length of the corridor. -/
namespace SlidingPuzzle
noncomputable section
open Classical

variable {n : ℕ} [NeZero n]

/-- Slide the blank along an embedded line from `a` to `b`. All encountered
tiles belong to `S`. Beyond `cap`, each tile moves one unit closer to its target,
so only the initial `cap-a` moves can be inefficient. The endpoint retains
membership in `S` and fixes every cell outside the traversed segment. -/
theorem exists_increasing_corridor_path
    (line : Fin n → Cell n) (hinj : Function.Injective line)
    (hadj : ∀ x y : Fin n, x.val + 1 = y.val → gridDistance (line x) (line y) = 1)
    (S : Set (Tile n)) (cap : ℕ)
    (hefficient : ∀ (x y : Fin n) (t : Tile n), x.val + 1 = y.val →
      cap ≤ x.val → t ∈ S →
      gridDistance (line x) (position (target n) t) + 1 =
        gridDistance (line y) (position (target n) t))
    (a b : Fin n) (hab : a ≤ b) (B : Board n) (hblank : blank B = line a)
    (hgroup : ∀ x : Fin n, a ≤ x → x ≤ b → x ≠ a → B (line x) ∈ S) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = line b ∧ p.length = b.val - a.val ∧
      p.inefficientMoves ≤ cap - a.val ∧
      (∀ x : Fin n, a ≤ x → x ≤ b → x ≠ b → C (line x) ∈ S) ∧
      (∀ c : Cell n, (∀ x : Fin n, a ≤ x → x ≤ b → c ≠ line x) → C c = B c) := by
  generalize hd : b.val - a.val = d
  induction d generalizing a B with
  | zero =>
    have heq : a = b := Fin.ext (by omega)
    subst a
    refine ⟨B, .nil B, hblank, by simp, by simp [Path.inefficientMoves], ?_, ?_⟩
    · intro x hx hxb hne
      exact (hne (le_antisymm hxb hx)).elim
    · intros; rfl
  | succ d ih =>
    let a' : Fin n := ⟨a.val + 1, by omega⟩
    have haa' : a < a' := by change a.val < a.val + 1; omega
    have ha'b : a' ≤ b := by change a.val + 1 ≤ b.val; omega
    have hneq : line a' ≠ blank B := by
      rw [hblank]
      exact fun h => (ne_of_gt haa') (hinj h)
    have hstep : gridDistance (blank B) (line a') = 1 := by
      rw [hblank]; exact hadj a a' rfl
    let B' := swapCells B (blank B) (line a')
    have hb' : blank B' = line a' := blank_swapCells B _
    have hg' : ∀ x : Fin n, a' ≤ x → x ≤ b → x ≠ a' → B' (line x) ∈ S := by
      intro x hx hxb hne
      rw [show B' (line x) = B (line x) from swapCells_preserves B
        (by rw [hblank]; exact fun h => (by have := hinj h; subst x; exact (not_le_of_gt haa') hx))
        (fun h => hne (hinj h))]
      exact hgroup x (haa'.le.trans hx) hxb (ne_of_gt (haa'.trans_le hx))
    obtain ⟨C, p, hc, hp, he, hg, hfix⟩ := ih a' ha'b B' hb' hg' (by dsimp [a']; omega)
    refine ⟨C, .cons ⟨line a', hstep, rfl⟩ p, hc, ?_, ?_, ?_, ?_⟩
    · change p.length + 1 = d + 1
      omega
    · change p.inefficientMoves + (if manhattan B < manhattan B' then 1 else 0) ≤ _
      by_cases hcap : cap ≤ a.val
      · have htile := hgroup a' haa'.le ha'b (ne_of_gt haa')
        have hdistance := hefficient a a' (B (line a')) rfl hcap htile
        have hbalance := manhattan_blank_swap_balance B (line a') hneq
        rw [hblank] at hbalance
        have hpot : ¬ manhattan B < manhattan B' := by dsimp [B']; rw [hblank]; omega
        simp only [hpot, ↓reduceIte, Nat.add_zero]
        dsimp [a'] at he
        omega
      · dsimp [a'] at he
        split_ifs <;> omega
    · intro x hx hxb hne
      by_cases hxa : x = a
      · subst x
        rw [hfix (line a) (by
          intro y hy _ heq
          have := hinj heq
          subst y
          exact (not_le_of_gt haa') hy)]
        change swapCells B (blank B) (line a') (line a) ∈ S
        rw [← hblank, swapCells_at_left]
        exact hgroup a' haa'.le ha'b (ne_of_gt haa')
      · exact hg x (by change a.val + 1 ≤ x.val; have hv : x.val ≠ a.val := fun h => hxa (Fin.ext h); omega) hxb hne
    · intro c hout
      rw [hfix c (fun x hx hxb => hout x (haa'.le.trans hx) hxb)]
      exact swapCells_preserves B (by rw [hblank]; exact hout a le_rfl hab)
        (hout a' haa'.le ha'b)

/-- Coordinates on a horizontal (`vertical = false`) or vertical line.
`backwards = true` reverses the varying coordinate, so increasing ranks move
left or up. -/
def corridorCell (vertical backwards : Bool) (fixed x : Fin n) : Cell n :=
  let y := if backwards then x.rev else x
  if vertical then (y, fixed) else (fixed, y)

/-- The coordinate which varies along a corridor. -/
def corridorCoordinate (vertical : Bool) (c : Cell n) : ℕ :=
  if vertical then c.1.val else c.2.val

/-- In any of the four directions, a corridor starting in the target interval
costs at most its width in inefficient moves, regardless of its total length.
The hypotheses concern actual tile targets, not a replacement potential. -/
theorem exists_oriented_corridor_path
    (vertical backwards : Bool) (fixed a b : Fin n) (hab : a ≤ b)
    (S : Set (Tile n)) (lo hi : ℕ)
    (htarget : ∀ t ∈ S, lo ≤ corridorCoordinate vertical (position (target n) t) ∧
      corridorCoordinate vertical (position (target n) t) < hi)
    (hstart : lo ≤ corridorCoordinate vertical (corridorCell vertical backwards fixed a) ∧
      corridorCoordinate vertical (corridorCell vertical backwards fixed a) < hi)
    (B : Board n) (hblank : blank B = corridorCell vertical backwards fixed a)
    (hgroup : ∀ x : Fin n, a ≤ x → x ≤ b → x ≠ a →
      B (corridorCell vertical backwards fixed x) ∈ S) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = corridorCell vertical backwards fixed b ∧ p.length = b.val - a.val ∧
      p.inefficientMoves ≤ hi - lo ∧
      p.inefficientMoves ≤ (if backwards then n - lo else hi) - a.val ∧
      (∀ x : Fin n, a ≤ x → x ≤ b → x ≠ b →
        C (corridorCell vertical backwards fixed x) ∈ S) ∧
      (∀ c : Cell n, (∀ x : Fin n, a ≤ x → x ≤ b →
        c ≠ corridorCell vertical backwards fixed x) → C c = B c) := by
  let line := corridorCell vertical backwards fixed
  let cap := if backwards then n - lo else hi
  have hinj : Function.Injective line := by
    intro x y h
    cases vertical <;> cases backwards <;>
      simp_all [line, corridorCell, Fin.rev_inj]
  have hadj : ∀ x y : Fin n, x.val + 1 = y.val → gridDistance (line x) (line y) = 1 := by
    intro x y h
    cases vertical <;> cases backwards <;>
      simp [line, corridorCell, gridDistance, Fin.rev, Nat.dist] <;> omega
  have hefficient : ∀ (x y : Fin n) (t : Tile n), x.val + 1 = y.val →
      cap ≤ x.val → t ∈ S →
      gridDistance (line x) (position (target n) t) + 1 =
        gridDistance (line y) (position (target n) t) := by
    intro x y t hxy hcap ht
    have ht' := htarget t ht
    cases vertical <;> cases backwards <;>
      simp only [line, cap, corridorCell, corridorCoordinate, Bool.false_eq_true,
        ↓reduceIte, gridDistance, Fin.rev, Nat.dist] at ht' hcap ⊢ <;> omega
  obtain ⟨C, p, hb, hp, he, hg, hf⟩ :=
    exists_increasing_corridor_path line hinj hadj S cap hefficient a b hab B hblank hgroup
  refine ⟨C, p, hb, hp, he.trans ?_, he, hg, hf⟩
  cases vertical <;> cases backwards <;>
    simp_all [cap, corridorCoordinate, corridorCell, Fin.rev] <;> omega

end
end SlidingPuzzle
