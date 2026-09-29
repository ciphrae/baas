import SlidingPuzzle.Tree.ReserveAccounting
import SlidingPuzzle.Tree.Hier

/-! # Tight lane systems

The axiom `sum_len` allows `2·depth·k` blocks of pieces landing at one block. In the
`b`-ary hierarchy the pieces at level `ℓ` have length at most `(b-1)·b^(h-ℓ-1)`, so
the total is below `2k` whatever the depth. Then the reserve a square needs, and the
ports, do not grow with the depth. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ} (L : LaneSys k q)

/-- The pieces landing at a block have total length at most `2k`. -/
def LaneSys.Tight : Prop := ∀ t : Fin k, ∑ o, ∑ side, L.len o t side ≤ 2 * k

theorem sum_axis_le' (c M : ℕ) (ht : ∀ t : Fin k, ∑ o, ∑ side, L.len o t side ≤ M) (T : Fin k) :
    (∑ o : Fin q, ∑ side : Bool, (c * L.len o T side + 2 * k)) ≤ c * M + 4 * k * q := by
  have h1 : (∑ o : Fin q, ∑ side : Bool, (c * L.len o T side + 2 * k)) =
      c * (∑ o, ∑ side, L.len o T side) + 4 * k * q := by
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_bool,
      Fintype.card_fin, smul_eq_mul]
    ring
  rw [h1]
  have := Nat.mul_le_mul_left c (ht T)
  omega

/-- The reserve input of one square, for a tight lane system. -/
theorem needAt_le_tight (hT : L.Tight) (s lam : ℕ) (Q : Sq k) :
    needAt L s lam Q ≤ 2 * ((2 * s + 2 * k + (15 * lam + 1) * k) * (2 * k) + 4 * k * q) := by
  unfold needAt
  refine (sum_le_sum fun l _ => laneBud_add_X_le L s lam l).trans ?_
  rw [sum_lanes_at Q (fun l => (2 * s + 2 * k + (15 * lam + 1) * k) * blen L l.2 + 2 * k)]
  simp only [blen]
  have h1 := sum_axis_le' L (2 * s + 2 * k + (15 * lam + 1) * k) (2 * k) hT Q.1
  have h2 := sum_axis_le' L (2 * s + 2 * k + (15 * lam + 1) * k) (2 * k) hT Q.2
  omega

namespace Hier

variable {b h : ℕ}

theorem level_sum_tight (hb : 2 ≤ b) (t : Fin (b ^ h)) (ℓ : Fin h) (side : Bool) :
    ∑ i : Fin b, len b h (finProdFinEquiv (ℓ, i)) t side ≤ (b - 1) * b ^ (h - ℓ.val - 1) := by
  set m := b ^ (h - ℓ.val - 1)
  have hm : 0 < m := by positivity
  have hcsz : ∀ i : Fin b, csz b h (finProdFinEquiv (ℓ, i)) = m := by
    intro i; simp only [csz, lev_mk]; rfl
  apply sum_le_of_unique _ (fun i : Fin b => t.val % (b * m) =
    (if side then i.val * m + (m - 1) else i.val * m)) ((b - 1) * m)
  · intro i j hi hj
    apply Fin.ext
    have e := hi.symm.trans hj
    exact Nat.eq_of_mul_eq_mul_right hm (show i.val * m = j.val * m by split_ifs at e <;> omega)
  · intro i
    have hi := i.isLt
    simp only [len, chi_mk, hcsz]
    cases side
    · simp only [Bool.false_eq_true, if_false]
      split_ifs with h1
      · exact Nat.mul_le_mul_right _ (by omega)
      · exact Nat.zero_le _
    · simp only [if_true]
      split_ifs with h1
      · exact Nat.mul_le_mul_right _ (by omega)
      · exact Nat.zero_le _

theorem geom_sum_le (hb : 2 ≤ b) : ∀ h : ℕ, ∑ ℓ ∈ range h, (b - 1) * b ^ ℓ + 1 = b ^ h
  | 0 => by simp
  | h + 1 => by
    rw [sum_range_succ, pow_succ]
    have := geom_sum_le hb h
    have e : (b - 1) * b ^ h + b ^ h = b ^ h * b := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    omega

theorem tight (hb : 2 ≤ b) (hh : 0 < h) : (sys b h hb hh).Tight := by
  intro t
  show ∑ o, ∑ side, len b h o t side ≤ 2 * b ^ h
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  calc ∑ ℓ : Fin h, ∑ i : Fin b, ∑ side, len b h (finProdFinEquiv (ℓ, i)) t side
      = ∑ ℓ : Fin h, ∑ side, ∑ i : Fin b, len b h (finProdFinEquiv (ℓ, i)) t side := by
        refine sum_congr rfl fun ℓ _ => sum_comm
    _ ≤ ∑ ℓ : Fin h, ∑ _side : Bool, (b - 1) * b ^ (h - ℓ.val - 1) :=
        sum_le_sum fun ℓ _ => sum_le_sum fun side _ => level_sum_tight hb t ℓ side
    _ = 2 * ∑ ℓ ∈ range h, (b - 1) * b ^ ℓ := by
        simp only [sum_const, card_univ, Fintype.card_bool, smul_eq_mul]
        rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun ℓ => (b - 1) * b ^ (h - ℓ - 1))]
        rw [← sum_range_reflect]
        congr 1
        refine sum_congr rfl fun ℓ hℓ => ?_
        rw [mem_range] at hℓ
        congr 2
        omega
    _ ≤ 2 * b ^ h := by have := geom_sum_le hb h; omega

end Hier

end SlidingPuzzle.Tree
