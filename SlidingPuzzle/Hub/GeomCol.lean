import SlidingPuzzle.Hub.PrimRes
import SlidingPuzzle.Hub.PrimWalk

/-! # Geometry of a column corridor

Consecutive positions of a column half are either adjacent (same band) or
separated by a row group (`k+1` rows apart, an odd jump since `k` is even).
Clean tiles move toward their band on adjacent steps. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ} [NeZero n]

omit [NeZero n] in
/-- Position `p` of a hop2: inside the half, in the hub's band, at the row offset
next to the hub's row group (`k`, lower half) or at the bottom (`s-1`, upper). -/
theorem hop2_geom (hd : HDims n k s) {h D : Sq k} (hne : h.1 ≠ D.1) :
    hop2Pos s h D < colLen k s (hop2Half h D) ∧
    cBand k s (hop2Half h D) (hop2Pos s h D) = h.1.val ∧
    cOff k s (hop2Half h D) (hop2Pos s h D) = (if D.1 < h.1 then k else s - 1) := by
  have hne' : h.1.val ≠ D.1.val := fun e => hne (Fin.ext e)
  have hm : 0 < s - k := by have := hd.k_lt_s; omega
  have hb := h.1.isLt
  have ha := D.1.isLt
  have hdiv : ∀ x, x * (s - k) / (s - k) = x := fun x => Nat.mul_div_cancel x hm
  have hmod : ∀ x, x * (s - k) % (s - k) = 0 := fun x => Nat.mul_mod_left x (s - k)
  unfold hop2Pos hop2Half colLen cBand cOff
  simp only
  by_cases hlt : D.1 < h.1
  · have hlt' : D.1.val < h.1.val := hlt
    simp only [hlt, decide_true, if_true, hdiv, hmod]
    have e : Nat.dist h.1.val D.1.val - 1 = h.1.val - D.1.val - 1 := by unfold Nat.dist; omega
    rw [e]
    refine ⟨?_, by omega, by omega⟩
    apply Nat.mul_lt_mul_of_pos_right (by omega) hm
  · have hlt' : h.1.val < D.1.val := by
      have : ¬ D.1.val < h.1.val := hlt
      omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false, hdiv, hmod]
    have e : Nat.dist h.1.val D.1.val - 1 = D.1.val - h.1.val - 1 := by unfold Nat.dist; omega
    rw [e]
    refine ⟨?_, by omega, by omega⟩
    apply Nat.mul_lt_mul_of_pos_right (by omega) hm

omit [NeZero n] in
theorem cBand_zero (V : ColH k) :
    cBand k s V 0 = (if V.2.2 then V.2.1.val + 1 else V.2.1.val - 1) ∧
    cOff k s V 0 = (if V.2.2 then k else s - 1) := by
  unfold cBand cOff; simp

/-- Two consecutive positions of a column half. -/
theorem colCell_step (hd : HDims n k s) (V : ColH k) (q : ℕ) (hq : q + 1 < colLen k s V) :
    (colCell (n := n) k s V q).2 = (colCell (n := n) k s V (q + 1)).2 ∧
    (((q + 1) % (s - k) = 0 ∧
        Nat.dist (colCell (n := n) k s V q).1.val (colCell (n := n) k s V (q + 1)).1.val = k + 1) ∨
      ((q + 1) % (s - k) ≠ 0 ∧
        (V.2.2 = true → (colCell (n := n) k s V (q + 1)).1.val =
          (colCell (n := n) k s V q).1.val + 1) ∧
        (V.2.2 = false → (colCell (n := n) k s V q).1.val =
          (colCell (n := n) k s V (q + 1)).1.val + 1))) := by
  have hm : 0 < s - k := by have := hd.k_lt_s; omega
  refine ⟨Fin.ext (by rw [colCell_snd hd, colCell_snd hd]), ?_⟩
  rw [colCell_fst hd V q (by omega), colCell_fst hd V (q + 1) hq]
  have hdq := colPos_div_lt hd V (q + 1) hq
  have hks := hd.k_lt_s
  unfold cBand cOff
  rcases divmod_succ hm q with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    refine ⟨h1, ?_⟩
    rw [h2] at hdq
    rw [h1, h2]
    cases e : V.2.2
    · simp only [e, Bool.false_eq_true, if_false] at hdq ⊢
      generalize q / (s - k) = x at *
      generalize q % (s - k) = y at *
      have : (V.2.1.val - 1 - x) * s = (V.2.1.val - 1 - (x + 1)) * s + s := by
        rw [← add_one_mul]; congr 1; omega
      simp only [Nat.dist]; omega
    · simp only [e, if_true] at hdq ⊢
      generalize q / (s - k) = x at *
      generalize q % (s - k) = y at *
      have : (V.2.1.val + 1 + (x + 1)) * s = (V.2.1.val + 1 + x) * s + s := by ring
      simp only [Nat.dist]; omega
  · right
    refine ⟨by omega, ?_, ?_⟩ <;> intro e <;> rw [h1, h2] <;> simp only [e, Bool.false_eq_true,
      if_false, if_true] <;> generalize q / (s - k) = x at * <;> omega

/-- Clean tiles (class of the column half) move toward their band on adjacent
steps. -/
theorem moveCost_colCell (hd : HDims n k s) (V : ColH k) (q : ℕ) (hq : q + 1 < colLen k s V)
    (hstep : (q + 1) % (s - k) ≠ 0) (T : Tile n) (hT : (classOf hd T).1 = V.2.1) :
    moveCost (colCell (n := n) k s V q) (colCell k s V (q + 1)) T = 0 := by
  have hr : (position (target n) T).1.val / s = V.2.1.val := by
    have := congrArg Fin.val hT
    simpa [classOf, sqOf] using this
  have hb := (div_eq_iff_bounds hd.s_pos).mp hr
  obtain ⟨hcol, hcase⟩ := colCell_step (n := n) hd V q hq
  rcases hcase with ⟨h1, -⟩ | ⟨-, hlow, hup⟩
  · exact absurd h1 hstep
  have r0 := colCell_fst (n := n) hd V q (by omega)
  have bb := cBand_bounds hd V q (by omega)
  have ob := cOff_bounds hd V q
  unfold moveCost
  rw [if_pos]
  simp only [gridDistance, hcol, Nat.dist]
  cases e : V.2.2
  · have := hup e
    have := bb.2.2.2 e
    have := band_lt_band s this
    omega
  · have := hlow e
    have := bb.2.2.1 e
    have := band_lt_band s this
    omega

end SlidingPuzzle.Hub
