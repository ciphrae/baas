import SlidingPuzzle.Hub.GeomRow

/-! # Geometry of hop1: the insertion position -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

/-- The insertion position lies in the half, in the source block's reservoir
column farthest from the hub (column offset `s-1` on the right, `k` on the
left). -/
theorem hop1_geom (hd : HDims n k s) {S h : Sq k} (hne : S.2 ≠ h.2) :
    hop1Pos s S h < rowLen k s (hop1Half S h) ∧
    rowCol s (hop1Half S h) (hop1Pos s S h) =
      (if (hop1Half S h).2.2 then S.2.val * s + s - 1 else S.2.val * s + k) := by
  have hne' : S.2.val ≠ h.2.val := fun e => hne (Fin.ext e)
  have hJ := S.2.isLt
  have hc := h.2.isLt
  have hks := hd.k_lt_s
  have hs := hd.s_pos
  unfold hop1Pos insPos hop1Half hop1Dist rowLen rowCol
  simp only
  by_cases hlt : h.2 < S.2
  · have hlt' : h.2.val < S.2.val := hlt
    simp only [hlt, decide_true, if_true]
    obtain ⟨m, hm⟩ : ∃ m, S.2.val = h.2.val + 1 + m := ⟨S.2.val - h.2.val - 1, by omega⟩
    have hd1 : Nat.dist S.2.val h.2.val - 1 + 1 = m + 1 := by
      unfold Nat.dist; omega
    rw [hd1]
    have e1 : S.2.val * s = h.2.val * s + (m + 1) * s := by rw [hm]; ring
    obtain ⟨r, hr⟩ : ∃ r, k - 1 - h.2.val = m + 1 + r := ⟨k - 1 - h.2.val - (m + 1), by omega⟩
    have e2 : (k - 1 - h.2.val) * s = (m + 1) * s + r * s := by rw [hr]; ring
    have e3 : s ≤ (m + 1) * s := by nlinarith
    constructor <;> omega
  · have hlt' : S.2.val < h.2.val := by
      have : ¬ h.2.val < S.2.val := hlt
      omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    obtain ⟨m, hm⟩ : ∃ m, h.2.val = S.2.val + 1 + m := ⟨h.2.val - S.2.val - 1, by omega⟩
    have hd1 : Nat.dist S.2.val h.2.val - 1 + 1 = m + 1 := by
      unfold Nat.dist; omega
    rw [hd1]
    have e1 : h.2.val * s = S.2.val * s + (m + 1) * s := by rw [hm]; ring
    have e3 : s ≤ (m + 1) * s := by nlinarith
    constructor <;> omega

end SlidingPuzzle.Hub
