import SlidingPuzzle.Tree.Transport
import SlidingPuzzle.Tree.Hier

/-! # Lane inventories and reserve totals for the tree algorithm

The polynomial estimate built on these totals is in `FineAccounting`. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {n k s q : ℕ} (L : LaneSys k q)

theorem sum_laneI (f : LaneI k q → ℕ) :
    ∑ H, f H = ∑ b : Fin k, ∑ o : Fin q, ∑ t : Fin k, ∑ side : Bool,
      f ⟨b, o, t, side⟩ := by
  let e : LaneI k q ≃ Fin k × Fin q × Fin k × Bool :=
    ⟨fun H => (H.b, H.o, H.t, H.side), fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  simpa only [Fintype.sum_prod_type, e, Equiv.coe_fn_mk] using
    (Equiv.sum_comp e (fun p => f ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩))

theorem sum_blen_le : ∑ H : LaneI k q, blen L H ≤ k ^ 2 * q := by
  rw [sum_laneI]
  calc
    _ ≤ ∑ _b : Fin k, ∑ _o : Fin q, k := by
      apply sum_le_sum; intro b _
      apply sum_le_sum; intro o _
      exact L.sum_len_offset o
    _ = _ := by simp; ring

theorem laneCells_bound : laneCells L s ≤ 2 * k ^ 2 * q * s := by
  unfold laneCells rowLen colLen
  rw [← sum_mul, ← sum_mul]
  have h1 := Nat.mul_le_mul_right s (sum_blen_le L)
  have h2 := Nat.mul_le_mul (sum_blen_le L) (Nat.sub_le s q)
  nlinarith

theorem sum_blen_axes_le : ∑ l : Ln k q, blen L l.2 ≤ 2 * k ^ 2 * q := by
  simp only [Ln, Fintype.sum_prod_type, Fintype.sum_bool]
  have := sum_blen_le L
  nlinarith

theorem sum_Xs_le : ∑ l : Ln k q, (Xs L l).card ≤ 2 * k ^ 3 * q := by
  calc
    _ ≤ ∑ l : Ln k q, k * blen L l.2 := sum_le_sum fun l _ => card_Xs_le L l
    _ = k * ∑ l : Ln k q, blen L l.2 := (mul_sum ..).symm
    _ ≤ k * (2 * k ^ 2 * q) := Nat.mul_le_mul_left _ (sum_blen_axes_le L)
    _ = _ := by ring

/-- A global reserve-input bound; the logarithmic term remains explicit. -/
theorem total_need_le (lam : ℕ) :
    ∑ v, needAt L s lam v ≤ 4 * k ^ 2 * q * s + (14 + 30 * lam) * k ^ 3 * q := by
  rw [sum_needAt]
  simp only [laneBud]
  simp_rw [mul_add, add_mul, sum_add_distrib]
  simp_rw [← mul_sum, ← sum_mul]
  have hl := sum_blen_axes_le L
  have hx := sum_Xs_le L
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [card_Ln]
  simp_rw [← mul_sum]
  nlinarith [Nat.mul_le_mul_left (2 * s + 2 * k) hl,
    Nat.mul_le_mul_left (15 * lam + 1) hx]

theorem total_resv_le [NeZero n] (td : TDims n k s q) :
    ∑ Q, resv L n s Q ≤
      6 * k ^ 2 * q * s + (14 + 30 * GroupedOrder.lamN n) * k ^ 3 * q + 6 * k ^ 2 := by
  simp only [resv, Rneed, sum_add_distrib]
  rw [sum_regionSize (n := n) L td]
  have hn := total_need_le (s := s) L (GroupedOrder.lamN n)
  have hl := laneCells_bound (s := s) L
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  nlinarith

end SlidingPuzzle.Tree
