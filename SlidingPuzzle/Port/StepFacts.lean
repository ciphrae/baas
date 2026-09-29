import SlidingPuzzle.Port.Simulate
import SlidingPuzzle.Tree.RunMain

/-! # Facts about abstract port steps

The effect of each event on lanes, region counts and port counts, and the junk
potential through a hop. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq shiftIn incCnt decCnt incCnt_apply decCnt_apply sum_update_add
  card_filter_shiftIn)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

theorem step_hop_cnt (s : ℕ) (ρ : PState k q) (l : Ln k q) (J : Fin k) (y : Sq k) (m : Mode k) :
    (ρ.step s (.hop l J y m)).cnt = incCnt (decCnt ρ.cnt (src l J) y) (land l) (ρ.lane l 0) := rfl

theorem step_hop_pc (s : ℕ) (ρ : PState k q) (l : Ln k q) (J : Fin k) (y : Sq k) (m : Mode k) :
    (ρ.step s (.hop l J y m)).pc =
      PState.srcPc (incP ρ.pc (land l) (lport l) (ρ.lane l 0)) (src l J) (lport l) y m := rfl

theorem step_hop_blank (s : ℕ) (ρ : PState k q) (l : Ln k q) (J : Fin k) (y : Sq k) (m : Mode k) :
    (ρ.step s (.hop l J y m)).blank = src l J ∧ (ρ.step s (.hop l J y m)).bp = lport l :=
  ⟨rfl, rfl⟩

theorem lposP_lt {n s : ℕ} [NeZero n] (td : TDims n k s q) (l : Ln k q) (J : Fin k) (hJ : LIn L l.2 J) :
    lposP k s l J < llen L s l := by
  obtain ⟨a, H⟩ := l
  cases a
  · exact (rowPos_geom (n := n) L td H J hJ).1
  · exact (colPosP_geom L td H J hJ).1

/-- A hop pays its junk steps from the potential; a junk insertion adds at most its position
plus one. -/
theorem pot_hop {n s : ℕ} [NeZero n] (td : TDims n k s q) (ρ : PState k q) (l : Ln k q) (J : Fin k)
    (hJ : LIn L l.2 J) (y : Sq k) (m : Mode k) :
    (ρ.step s (.hop l J y m)).pot L s + ρ.ljunk l (lposP k s l J) =
      ρ.pot L s + (if ¬ lgood l y then lposP k s l J + 1 else 0) := by
  unfold PState.pot PState.ljunk
  rw [step_hop_lane s ρ l J y m]
  have hsum := sum_update_add
    (fun (l' : Ln k q) (f : ℕ → Sq k) =>
      ∑ r ∈ (range (llen L s l')).filter (fun r => ¬ lgood l' (f r)), (r + 1))
    ρ.lane l (shiftIn (ρ.lane l) (lposP k s l J) y)
  have hc := sum_filter_shiftIn' (fun a : Sq k => ¬ lgood l a) (ρ.lane l)
    (lposP_lt L td l J hJ) y
  omega

theorem pot_xfer (s : ℕ) (ρ : PState k q) (pt : Pt) (c : Sq k) :
    (ρ.step s (.xfer pt c)).pot L s = ρ.pot L s := rfl

theorem pot_leg (s : ℕ) (ρ : PState k q) (Z y : Sq k) (p : Part) (z : Sq k) :
    (ρ.step s (.leg Z y p z)).pot L s = ρ.pot L s := rfl

theorem ppot_le (s : ℕ) (ρ : PState k q) : ρ.pot L s ≤ laneCells L s * (k * s) := by
  unfold PState.pot
  have h1 : ∀ l : Ln k q, ∑ r ∈ (range (llen L s l)).filter (fun r => ¬ lgood l (ρ.lane l r)), (r + 1)
      ≤ llen L s l * (k * s) := by
    intro l
    calc _ ≤ ∑ r ∈ range (llen L s l), (k * s) := by
          refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)) (sum_le_sum fun r hr => ?_)
          have := llen_le L s l; simp at hr; omega
      _ = llen L s l * (k * s) := by simp
  refine (sum_le_sum fun l _ => h1 l).trans ?_
  rw [← sum_mul]
  apply Nat.mul_le_mul_right
  unfold laneCells
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [llen, add_comm]

end SlidingPuzzle.Port
