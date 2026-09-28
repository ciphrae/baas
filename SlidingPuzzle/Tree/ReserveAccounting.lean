import SlidingPuzzle.Tree.Transport

/-! # Local reserve estimates for the tree construction -/

namespace SlidingPuzzle.Tree

open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

/-- Split the lanes landing at a square into its row and column families. -/
theorem sum_lanes_at (Q : Sq k) (f : Ln k q → ℕ) :
    (∑ l ∈ univ.filter (fun l : Ln k q => land l = Q), f l) =
      (∑ o : Fin q, ∑ side : Bool, f (false, ⟨Q.1, o, Q.2, side⟩)) +
      (∑ o : Fin q, ∑ side : Bool, f (true, ⟨Q.2, o, Q.1, side⟩)) := by
  classical
  rw [sum_filter]
  simp_rw [Ln, Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  let e : LaneI k q ≃ Fin k × Fin q × Fin k × Bool :=
    ⟨fun H => (H.b, H.o, H.t, H.side),
      fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [← Equiv.sum_comp e.symm, ← Equiv.sum_comp e.symm]
  simp_rw [Fintype.sum_prod_type]
  rcases Q with ⟨a, b⟩
  simp only [land, rowLand, colLand, e, Prod.mk.injEq]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    simp [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- A single lane's budget and tag support are controlled by its length. -/
theorem laneBud_add_X_le (s lam : ℕ) (l : Ln k q) :
    laneBud L s lam l + (Xs L l).card ≤
      (2 * s + 2 * k + (15 * lam + 1) * k) * blen L l.2 + 2 * k := by
  have hX := card_Xs_le L l
  unfold laneBud
  calc
    _ ≤ 2 * blen L l.2 * s + 2 * k * (blen L l.2 + 1) +
        (15 * lam + 1) * (k * blen L l.2) := by
      nlinarith
    _ = _ := by ring

/-- Every piece length at a landing block is bounded by the total piece length
allowed by the lane system. -/
theorem len_le_at_landing (l : Ln k q) :
    L.len l.2.o l.2.t l.2.side ≤ 2 * L.depth * k := by
  have hs : L.len l.2.o l.2.t l.2.side ≤ ∑ side, L.len l.2.o l.2.t side :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
  have ho : (∑ side, L.len l.2.o l.2.t side) ≤ ∑ o, ∑ side, L.len o l.2.t side :=
    single_le_sum (f := fun o : Fin q => ∑ side, L.len o l.2.t side)
      (fun _ _ => Nat.zero_le _) (mem_univ _)
  exact hs.trans (ho.trans (L.sum_len l.2.t))

end SlidingPuzzle.Tree

namespace SlidingPuzzle.Tree

open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

/-- The lanes of one axis landing at a block share the piece lengths of that block. -/
theorem sum_axis_le (c : ℕ) (ht : ∀ t : Fin k, ∑ o, ∑ side, L.len o t side ≤ 2 * L.depth * k)
    (T : Fin k) :
    (∑ o : Fin q, ∑ side : Bool, (c * L.len o T side + 2 * k)) ≤
      c * (2 * L.depth * k) + 4 * k * q := by
  have h1 : (∑ o : Fin q, ∑ side : Bool, (c * L.len o T side + 2 * k)) =
      c * (∑ o, ∑ side, L.len o T side) + 4 * k * q := by
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_bool,
      Fintype.card_fin, smul_eq_mul]
    ring
  rw [h1]
  have := Nat.mul_le_mul_left c (ht T)
  omega

/-- The reserve input of one square. -/
theorem needAt_le (s lam : ℕ) (Q : Sq k) :
    needAt L s lam Q ≤
      2 * ((2 * s + 2 * k + (15 * lam + 1) * k) * (2 * L.depth * k) + 4 * k * q) := by
  unfold needAt
  refine (sum_le_sum fun l _ => laneBud_add_X_le L s lam l).trans ?_
  rw [sum_lanes_at Q (fun l => (2 * s + 2 * k + (15 * lam + 1) * k) * blen L l.2 + 2 * k)]
  simp only [blen]
  have h1 := sum_axis_le L (2 * s + 2 * k + (15 * lam + 1) * k) L.sum_len Q.1
  have h2 := sum_axis_le L (2 * s + 2 * k + (15 * lam + 1) * k) L.sum_len Q.2
  omega

end SlidingPuzzle.Tree
