import SlidingPuzzle.Port.Leg

/-! # Relocation legs on boards -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf sqDist apply_blank blank_eq_of_apply
  val_ne_zero_of_ne_blank exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist
  InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- The jump axis of a leg: along rows when the squares share their band. -/
def legHor (E Z : Sq k) : Bool := decide (E.1 = Z.1)

/-- The parity shift of a leg. -/
def legJ (s : ℕ) (E Z : Sq k) : ℕ :=
  if E.1 = Z.1 then (E.2.val * s + Z.2.val * s + 1) % 2 else (E.1.val * s + Z.1.val * s + 1) % 2

omit [NeZero n] in
theorem sqDist_comm (E Z : Sq k) : sqDist E Z = sqDist Z E := by
  unfold sqDist; rw [Nat.dist_comm E.1.val, Nat.dist_comm E.2.val]

/-- The jumps of a leg, both ways. -/
theorem leg_jump (pd : PDims n k s q σ) (h8 : 8 ≤ σ) {E Z : Sq k} (hal : E.1 = Z.1 ∨ E.2 = Z.2)
    (b : Pt) {m : ℕ} (hm : m ≤ 4) :
    (∀ B' : Board n, blank B' = lc s E (ncell k s b).1 (ncell k s b).2 →
      ∃ p : Path B' (swapCells B' (blank B')
        (lc s Z (lz k s b (legHor E Z) (legJ s E Z) m).1 (lz k s b (legHor E Z) (legJ s E Z) m).2)),
        p.inefficientMoves ≤ 7 * (sqDist E Z * s + 5)) ∧
    (∀ B' : Board n, blank B' =
        lc s Z (lz k s b (legHor E Z) (legJ s E Z) m).1 (lz k s b (legHor E Z) (legJ s E Z) m).2 →
      ∃ p : Path B' (swapCells B' (blank B') (lc s E (ncell k s b).1 (ncell k s b).2)),
        p.inefficientMoves ≤ 7 * (sqDist E Z * s + 5)) ∨ m % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one m with hme | hme
  swap
  · exact Or.inr hme
  left
  have hf := pd.fit
  have hj : legJ s E Z ≤ 1 := by unfold legJ; split_ifs <;> omega
  obtain ⟨-, -, -, hH, hV, -, a1, a2, z1, z2⟩ := lgeom (k := k) h8 hf b (legHor E Z) hj hm
  set a := ncell k s b
  set z := lz k s b (legHor E Z) (legJ s E Z) m
  have hdist : Nat.dist a.1 z.1 ≤ 4 ∧ Nat.dist a.2 z.2 ≤ 4 := by
    by_cases h : E.1 = Z.1
    · obtain ⟨r1, r2, -, -, d⟩ := hH (by simp [legHor, h])
      exact ⟨by simp only [Nat.dist]; omega, by omega⟩
    · obtain ⟨r1, r2, -, -, d⟩ := hV (by simp [legHor, h])
      exact ⟨by omega, by simp only [Nat.dist]; omega⟩
  have hal' : (E.1 = Z.1 ∧ a.1 ≤ z.1 + 1 ∧ z.1 ≤ a.1 + 1) ∨
      (E.2 = Z.2 ∧ a.2 ≤ z.2 + 1 ∧ z.2 ≤ a.2 + 1) := by
    by_cases h : E.1 = Z.1
    · obtain ⟨r1, r2, -, -, -⟩ := hH (by simp [legHor, h]); exact Or.inl ⟨h, r2, r1⟩
    · obtain ⟨r1, r2, -, -, -⟩ := hV (by simp [legHor, h])
      exact Or.inr ⟨hal.resolve_left h, r2, r1⟩
  have hpar : (E.1.val * s + a.1 + (E.2.val * s + a.2) + (Z.1.val * s + z.1) +
      (Z.2.val * s + z.2)) % 2 = 1 := by
    by_cases h : E.1 = Z.1
    · obtain ⟨-, -, p1, p2, -⟩ := hH (by simp [legHor, h])
      have e1 : E.1.val * s = Z.1.val * s := by rw [h]
      have ej : legJ s E Z = (E.2.val * s + Z.2.val * s + 1) % 2 := by simp [legJ, h]
      rw [ej] at p1
      omega
    · obtain ⟨-, -, p1, p2, -⟩ := hV (by simp [legHor, h])
      have h2 := hal.resolve_left h
      have e2 : E.2.val * s = Z.2.val * s := by rw [h2]
      have ej : legJ s E Z = (E.1.val * s + Z.1.val * s + 1) % 2 := by simp [legJ, h]
      rw [ej] at p1
      omega
  refine ⟨fun B' hB' => jump_cross pd E Z a1 a2 z1 z2 hal' hpar hdist B' hB', fun B' hB' => ?_⟩
  have hal'' : (Z.1 = E.1 ∧ z.1 ≤ a.1 + 1 ∧ a.1 ≤ z.1 + 1) ∨
      (Z.2 = E.2 ∧ z.2 ≤ a.2 + 1 ∧ a.2 ≤ z.2 + 1) := by
    rcases hal' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1.symm, h3, h2⟩
    · exact Or.inr ⟨h1.symm, h3, h2⟩
  have := jump_cross pd Z E z1 z2 a1 a2 hal'' (by omega)
    ⟨by rw [Nat.dist_comm]; exact hdist.1, by rw [Nat.dist_comm]; exact hdist.2⟩ B' hB'
  rwa [sqDist_comm] at this

end SlidingPuzzle.Port
