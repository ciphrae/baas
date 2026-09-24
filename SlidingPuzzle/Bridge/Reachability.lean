import SlidingPuzzle.Bridge.Words
import SlidingPuzzle.OrbitParity
import Zhong.Reachable
import Zhong.Algorithm.TwoByTwo

/-! Transfer the proved parity sufficiency to the public legal-path model.
The general grid proof handles n ≥ 3; the checked 2×2 solving table handles n = 2. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

private theorem parity_eq_iff_sign (B : Board n) :
    parityInvariant B = colorSign (blank (target n)) ↔
      Equiv.Perm.sign (Zhong.relPerm (Zhong.target n n) B) =
        Zhong.cellParity (Zhong.blank (Zhong.target n n)) * Zhong.cellParity (Zhong.blank B) := by
  have hs : Equiv.Perm.sign (Zhong.relPerm (Zhong.target n n) B) = boardSign B := by
    rw [Zhong.sign_relPerm]
    simp only [Zhong.boardSign, Equiv.self_trans_symm, Equiv.Perm.sign_refl, one_mul]
    rfl
  rw [hs]
  change boardSign B * colorSign (blank B) = colorSign (blank (target n)) ↔
    boardSign B = colorSign (blank (target n)) * colorSign (blank B)
  have hb : colorSign (blank B) * colorSign (blank B) = 1 := Zhong.units_mul_self _
  constructor
  · intro h
    have hh := congrArg (fun x : ℤˣ => x * colorSign (blank B)) h
    simpa only [mul_assoc, hb, mul_one] using hh
  · intro h
    rw [h, mul_assoc, hb, mul_one]

/-- Every board satisfying the target parity condition is reachable for n ≥ 2. -/
theorem reachable_of_parityInvariant (hn : 2 ≤ n) (B : Board n)
    (h : parityInvariant B = colorSign (blank (target n))) : Reachable B := by
  have hs := (parity_eq_iff_sign B).mp h
  by_cases hn3 : 3 ≤ n
  · apply reachable_iff_zhong.mpr
    exact Zhong.reachable_of_sign_relPerm hn3 hn hs
  · have hn2 : n = 2 := by omega
    subst n
    have hrev : Equiv.Perm.sign (Zhong.relPerm B (Zhong.target 2 2)) =
        Zhong.cellParity (Zhong.blank B) * Zhong.cellParity (Zhong.blank (Zhong.target 2 2)) := by
      rw [Zhong.sign_relPerm] at hs ⊢
      simpa only [mul_comm] using hs
    have heff := Zhong.solve22_correct B hrev
    obtain ⟨p, _⟩ := path_of_zhong_word B (Zhong.solve22 B)
    rw [heff] at p
    exact ⟨p.reverse⟩

/-- The complete solvability criterion in the public model, including size two. -/
theorem reachable_iff_parityInvariant (hn : 2 ≤ n) (B : Board n) :
    Reachable B ↔ parityInvariant B = colorSign (blank (target n)) :=
  ⟨reachable_parityInvariant B, reachable_of_parityInvariant hn B⟩

end SlidingPuzzle
