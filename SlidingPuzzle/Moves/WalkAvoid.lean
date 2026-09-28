import SlidingPuzzle.Moves.BlankAccess
import SlidingPuzzle.Paths

/-! # Walks that avoid a corner

Inside a rectangle `[R0, R1] × [C0, C1]` the blank walks between any two cells
without touching the two cells `(R1, C1 - 1)` and `(R1, C1)` of the bottom-right
corner other than its start and end (`exists_rect_walk_avoid`): vertical then
horizontal, horizontal then vertical, or through the row above, depending on
which endpoints lie in the bottom row. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- A walk inside the rectangle that only changes cells of the rectangle and
keeps the corner cells other than its endpoints. -/
def RectWalk (R0 R1 C0 C1 : ℕ) (B C : Board n) (e : Cell n) (len : ℕ) : Prop :=
  blank C = e ∧ len ≤ (R1 - R0) + (C1 - C0) ∧
    (∀ x : Cell n, ¬ (R0 ≤ x.1.val ∧ x.1.val ≤ R1 ∧ C0 ≤ x.2.val ∧ x.2.val ≤ C1) → C x = B x) ∧
    (∀ x : Cell n, x.1.val = R1 → C1 ≤ x.2.val + 1 → x ≠ blank B → x ≠ e → C x = B x)

/-- One vertical-then-horizontal leg inside the rectangle. -/
theorem exists_leg (B : Board n) (R0 R1 C0 C1 : ℕ) (e : Cell n)
    (hb : R0 ≤ (blank B).1.val ∧ (blank B).1.val ≤ R1 ∧ C0 ≤ (blank B).2.val ∧ (blank B).2.val ≤ C1)
    (he : R0 ≤ e.1.val ∧ e.1.val ≤ R1 ∧ C0 ≤ e.2.val ∧ e.2.val ≤ C1) :
    ∃ C : Board n, ∃ p : Path B C, blank C = e ∧ p.length ≤ gridDistance (blank B) e ∧
      (∀ x : Cell n, ¬ (R0 ≤ x.1.val ∧ x.1.val ≤ R1 ∧ C0 ≤ x.2.val ∧ x.2.val ≤ C1) → C x = B x) ∧
      (∀ x : Cell n,
        ¬ (x.2 = (blank B).2 ∧ min (blank B).1.val e.1.val ≤ x.1.val ∧
            x.1.val ≤ max (blank B).1.val e.1.val) →
        ¬ (x.1 = e.1 ∧ min (blank B).2.val e.2.val ≤ x.2.val ∧
            x.2.val ≤ max (blank B).2.val e.2.val) → C x = B x) := by
  obtain ⟨C, p, hbC, hl, hf⟩ := exists_walk_vh B e
  refine ⟨C, p, hbC, hl, fun x hx => hf x ?_ ?_, hf⟩
  · rintro ⟨h1, h2, h3⟩; apply hx
    have := congrArg Fin.val h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨h1, h2, h3⟩; apply hx
    have := congrArg Fin.val h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Walk between two cells of the rectangle, avoiding the two bottom-right
corner cells other than the endpoints. -/
theorem exists_rect_walk_avoid (B : Board n) (R0 R1 C0 C1 : ℕ) (hR : R0 + 2 ≤ R1)
    (hR1 : R1 < n) (hC1 : C1 < n) (e : Cell n)
    (hb : R0 ≤ (blank B).1.val ∧ (blank B).1.val ≤ R1 ∧ C0 ≤ (blank B).2.val ∧ (blank B).2.val ≤ C1)
    (he : R0 ≤ e.1.val ∧ e.1.val ≤ R1 ∧ C0 ≤ e.2.val ∧ e.2.val ≤ C1) :
    ∃ C : Board n, ∃ p : Path B C, RectWalk R0 R1 C0 C1 B C e p.length := by
  have hrect : gridDistance (blank B) e ≤ (R1 - R0) + (C1 - C0) := by
    unfold gridDistance; simp only [Nat.dist]; omega
  have gd : ∀ x y : Cell n, gridDistance x y = Nat.dist x.1.val y.1.val + Nat.dist x.2.val y.2.val :=
    fun _ _ => rfl
  rcases (show (blank B).1.val < R1 ∨ (blank B).1.val = R1 by omega) with hb1 | hb1 <;>
    rcases (show e.1.val < R1 ∨ e.1.val = R1 by omega) with he1 | he1
  · -- one leg
    obtain ⟨C, p, hbC, hl, hr, hf⟩ := exists_leg B R0 R1 C0 C1 e hb he
    refine ⟨C, p, hbC, hl.trans hrect, hr, fun x hx1 hx2 hxb hxe => hf x ?_ ?_⟩
    · rintro ⟨-, h2, h3⟩; omega
    · rintro ⟨h1, -⟩; have := congrArg Fin.val h1; omega
  · -- horizontal, then vertical into the bottom row
    let m : Cell n := ((blank B).1, e.2)
    obtain ⟨C1', p1, hb1', hl1, hr1, hf1⟩ := exists_leg B R0 R1 C0 C1 m hb
      ⟨hb.1, hb.2.1, he.2.2.1, he.2.2.2⟩
    have hbm : R0 ≤ (blank C1').1.val ∧ (blank C1').1.val ≤ R1 ∧ C0 ≤ (blank C1').2.val ∧
        (blank C1').2.val ≤ C1 := by rw [hb1']; exact ⟨hb.1, hb.2.1, he.2.2.1, he.2.2.2⟩
    obtain ⟨C, p2, hbC, hl2, hr2, hf2⟩ := exists_leg C1' R0 R1 C0 C1 e hbm he
    refine ⟨C, p1.append p2, hbC, ?_, fun x hx => by rw [hr2 x hx, hr1 x hx], ?_⟩
    · rw [Path.length_append]; rw [gd, hb1'] at hl2; rw [gd] at hl1
      simp only [Nat.dist, m] at hl1 hl2; omega
    · intro x hx1 hx2 hxb hxe
      have hxe' : x.2 ≠ e.2 := fun h => hxe (Prod.ext (Fin.ext (by omega)) h)
      have k1 : C1' x = B x := hf1 x
        (by rintro ⟨-, h2, h3⟩; simp only [m] at h2 h3; omega)
        (by rintro ⟨h1, -⟩; have := congrArg Fin.val h1; simp only [m] at this; omega)
      have k2 : C x = C1' x := hf2 x
        (by rintro ⟨h1, -⟩; rw [hb1'] at h1; exact hxe' h1)
        (by rintro ⟨-, h2, h3⟩; rw [hb1'] at h2 h3; simp only [m] at h2 h3
            exact hxe' (Fin.ext (by omega)))
      rw [k2, k1]
  · -- vertical out of the bottom row, then horizontal
    obtain ⟨C, p, hbC, hl, hr, hf⟩ := exists_leg B R0 R1 C0 C1 e hb he
    refine ⟨C, p, hbC, hl.trans hrect, hr, fun x hx1 hx2 hxb hxe => hf x ?_ ?_⟩
    · rintro ⟨h1, -⟩; exact hxb (Prod.ext (Fin.ext (by omega)) h1)
    · rintro ⟨h1, -⟩; have := congrArg Fin.val h1; omega
  · -- through the row above
    let m1 : Cell n := (⟨R1 - 1, by omega⟩, (blank B).2)
    let m2 : Cell n := (⟨R1 - 1, by omega⟩, e.2)
    obtain ⟨D1, q1, hq1b, hq1l, hq1r, hq1f⟩ := exists_leg B R0 R1 C0 C1 m1 hb
      ⟨by simp only [m1]; omega, by simp only [m1]; omega, hb.2.2.1, hb.2.2.2⟩
    have h1m : R0 ≤ (blank D1).1.val ∧ (blank D1).1.val ≤ R1 ∧ C0 ≤ (blank D1).2.val ∧
        (blank D1).2.val ≤ C1 := by
      rw [hq1b]; exact ⟨by simp only [m1]; omega, by simp only [m1]; omega, hb.2.2.1, hb.2.2.2⟩
    obtain ⟨D2, q2, hq2b, hq2l, hq2r, hq2f⟩ := exists_leg D1 R0 R1 C0 C1 m2 h1m
      ⟨by simp only [m2]; omega, by simp only [m2]; omega, he.2.2.1, he.2.2.2⟩
    have h2m : R0 ≤ (blank D2).1.val ∧ (blank D2).1.val ≤ R1 ∧ C0 ≤ (blank D2).2.val ∧
        (blank D2).2.val ≤ C1 := by
      rw [hq2b]; exact ⟨by simp only [m2]; omega, by simp only [m2]; omega, he.2.2.1, he.2.2.2⟩
    obtain ⟨C, q3, hq3b, hq3l, hq3r, hq3f⟩ := exists_leg D2 R0 R1 C0 C1 e h2m he
    refine ⟨C, (q1.append q2).append q3, hq3b, ?_,
      fun x hx => by rw [hq3r x hx, hq2r x hx, hq1r x hx], ?_⟩
    · simp only [Path.length_append]
      rw [gd, hq2b] at hq3l; rw [gd, hq1b] at hq2l; rw [gd] at hq1l
      simp only [Nat.dist, m1, m2] at hq1l hq2l hq3l; omega
    · intro x hx1 hx2 hxb hxe
      have hxb' : x.2 ≠ (blank B).2 := fun h => hxb (Prod.ext (Fin.ext (by omega)) h)
      have hxe' : x.2 ≠ e.2 := fun h => hxe (Prod.ext (Fin.ext (by omega)) h)
      have k1 : D1 x = B x := hq1f x
        (by rintro ⟨h1, -⟩; exact hxb' h1)
        (by rintro ⟨h1, -⟩; have := congrArg Fin.val h1; simp only [m1] at this; omega)
      have k2 : D2 x = D1 x := hq2f x
        (by rintro ⟨-, -, h3⟩; rw [hq1b] at h3; simp only [m1, m2] at h3; omega)
        (by rintro ⟨h1, -⟩; have := congrArg Fin.val h1; simp only [m2] at this; omega)
      have k3 : C x = D2 x := hq3f x
        (by rintro ⟨h1, -⟩; rw [hq2b] at h1; exact hxe' h1)
        (by rintro ⟨-, h2, h3⟩; rw [hq2b] at h2 h3; simp only [m2] at h2 h3
            exact hxe' (Fin.ext (by omega)))
      rw [k3, k2, k1]

end SlidingPuzzle
