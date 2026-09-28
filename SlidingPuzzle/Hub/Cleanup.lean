import SlidingPuzzle.Hub.Layout
import SlidingPuzzle.Moves.Exchange
import SlidingPuzzle.Moves.ThreeCycleSharp

/-! # Cleanup

Bring the blank into the last square, then fix misplaced tiles at least two at
a time: a misplaced tile goes to its square `Q` in exchange for a wrong tile of
`Q`, which goes to its own square by a three-cycle through a third wrong tile
(`exists_three_cycle_sharp`, `52 n`), or, if it belongs where the first tile
was, by a double swap (`exists_double_swap_sharp`, `104 n`) whose second
exchange stays inside one square and keeps the permutation even. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ}

namespace CleanupAux

open Finset LayoutFacts

/-- The misplaced-tile predicate of a board. -/
def Mis (hd : HDims n k s) (B : Board n) (x : Cell n) : Prop :=
  (B x).val ≠ 0 ∧ classOf hd (B x) ≠ sqOf hd x

instance (hd : HDims n k s) (B : Board n) (x : Cell n) : Decidable (Mis hd B x) := by
  unfold Mis; infer_instance

theorem misplaced_eq (hd : HDims n k s) (B : Board n) :
    misplaced hd B = #(univ.filter fun x => Mis hd B x) := rfl

/-- One move changes the misplaced count by at most one. -/
theorem misplaced_step (hd : HDims n k s) [NeZero n] {B C : Board n} (h : Step B C) :
    misplaced hd C ≤ misplaced hd B + 1 := by
  obtain ⟨c, -, rfl⟩ := h
  rw [misplaced_eq, misplaced_eq]
  refine (card_le_card (t := insert (blank B) (univ.filter fun x => Mis hd B x)) ?_).trans
    (card_insert_le _ _)
  intro x hx
  simp only [mem_filter, mem_univ, true_and, mem_insert] at hx ⊢
  by_cases hb : x = blank B
  · exact Or.inl hb
  right
  by_cases hc : x = c
  · subst hc
    exfalso
    apply hx.1
    simp [blank, position]
  · simpa [Mis, Equiv.swap_apply_of_ne_of_ne hb hc] using hx

theorem misplaced_path (hd : HDims n k s) [NeZero n] {B C : Board n} (p : Path B C) :
    misplaced hd C ≤ misplaced hd B + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := misplaced_step hd h
    simp only [Path.length_cons]
    omega

theorem sorted_of_misplaced_zero (hd : HDims n k s) {B : Board n} (h : misplaced hd B = 0) :
    ∀ x, (B x).val ≠ 0 → classOf hd (B x) = sqOf hd x := by
  intro x hx
  by_contra hne
  rw [misplaced_eq, card_eq_zero, filter_eq_empty_iff] at h
  exact h (mem_univ x) ⟨hx, hne⟩

/-- Square `Q` holds a nonblank tile of another class whenever some tile of
class `Q` lies outside `Q` (the blank being in the last square). -/
theorem exists_wrong_in_square (hd : HDims n k s) [NeZero n] (D : Board n)
    (hb : IsLast (sqOf hd (blank D))) (x1 : Cell n) (h1 : (D x1).val ≠ 0)
    (h1' : classOf hd (D x1) ≠ sqOf hd x1) :
    ∃ x2, sqOf hd x2 = classOf hd (D x1) ∧ (D x2).val ≠ 0 ∧
      classOf hd (D x2) ≠ classOf hd (D x1) := by
  set Q := classOf hd (D x1)
  by_contra hno
  push Not at hno
  let A := univ.filter fun z : Cell n => sqOf hd z = Q ∧ (D z).val ≠ 0
  let Cls := univ.filter fun x : Cell n => (D x).val ≠ 0 ∧ classOf hd (D x) = Q
  have hsub : A ⊂ Cls := by
    rw [ssubset_iff_of_subset]
    · refine ⟨x1, ?_, ?_⟩
      · simp only [Cls, mem_filter, mem_univ, true_and]
        exact ⟨h1, rfl⟩
      simp only [A, mem_filter, mem_univ, true_and, not_and]
      exact fun h => absurd h.symm h1'
    · intro z hz
      simp only [A, Cls, mem_filter, mem_univ, true_and] at hz ⊢
      exact ⟨hz.2, hno z hz.1 hz.2⟩
  have hlt := card_lt_card hsub
  have hCls : #Cls = s ^ 2 - if IsLast Q then 1 else 0 := card_class hd D Q
  have hsq := card_sqOf hd Q
  have hA : #(univ.filter fun z : Cell n => sqOf hd z = Q) ≤ #A + if IsLast Q then 1 else 0 := by
    split_ifs with hQ
    · refine (card_le_card (t := insert (blank D) A) ?_).trans (card_insert_le _ _)
      intro z hz
      simp only [A, mem_filter, mem_univ, true_and, mem_insert] at hz ⊢
      by_cases hzb : z = blank D
      · exact Or.inl hzb
      · exact Or.inr ⟨hz, val_ne_zero_of_ne_blank hzb⟩
    · refine card_le_card fun z hz => ?_
      simp only [A, mem_filter, mem_univ, true_and] at hz ⊢
      refine ⟨hz, val_ne_zero_of_ne_blank fun hzb => hQ ?_⟩
      rw [← hz, hzb]
      exact hb
  have hs := hs_pos hd
  have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
  split_ifs at hCls hA <;> omega

/-- If two distinct tiles of class `Q` lie outside `Q`, then `Q` holds a wrong
nonblank tile other than any given cell `w`. -/
theorem exists_wrong_in_square_ne (hd : HDims n k s) [NeZero n] (D : Board n)
    (hb : IsLast (sqOf hd (blank D))) (x1 y w : Cell n) (hxy : x1 ≠ y)
    (h1 : (D x1).val ≠ 0) (h1' : classOf hd (D x1) ≠ sqOf hd x1)
    (hy : (D y).val ≠ 0) (hy' : classOf hd (D y) ≠ sqOf hd y)
    (hcls : classOf hd (D y) = classOf hd (D x1)) :
    ∃ x2, sqOf hd x2 = classOf hd (D x1) ∧ (D x2).val ≠ 0 ∧
      classOf hd (D x2) ≠ classOf hd (D x1) ∧ x2 ≠ w := by
  set Q := classOf hd (D x1)
  by_contra hno
  push Not at hno
  let A := univ.filter fun z : Cell n => sqOf hd z = Q ∧ (D z).val ≠ 0
  let Cls := univ.filter fun x : Cell n => (D x).val ≠ 0 ∧ classOf hd (D x) = Q
  have hsub : A.erase w ⊆ (Cls.erase x1).erase y := by
    intro z hz
    simp only [A, Cls, mem_erase, mem_filter, mem_univ, true_and] at hz ⊢
    obtain ⟨hzw, hzQ, hz0⟩ := hz
    refine ⟨fun e => hy' (by rw [hcls, ← e, hzQ]), fun e => h1' (by rw [← e, hzQ]), hz0, ?_⟩
    by_contra hc
    exact hzw (hno z hzQ hz0 hc)
  have hx1m : x1 ∈ Cls := by simp only [Cls, mem_filter, mem_univ, true_and]; exact ⟨h1, rfl⟩
  have hym : y ∈ Cls.erase x1 := by
    simp only [Cls, mem_erase, mem_filter, mem_univ, true_and]; exact ⟨Ne.symm hxy, hy, hcls⟩
  have hle := card_le_card hsub
  rw [card_erase_of_mem hym, card_erase_of_mem hx1m] at hle
  have hle2 : #A ≤ #(A.erase w) + 1 := by
    have := card_le_card (show A ⊆ insert w (A.erase w) from fun z hz => by
      rw [mem_insert, mem_erase]; by_cases h : z = w
      · exact Or.inl h
      · exact Or.inr ⟨h, hz⟩)
    exact this.trans (card_insert_le _ _)
  have h2 : 2 ≤ #Cls := by
    have := card_pos.mpr ⟨y, hym⟩
    rw [card_erase_of_mem hx1m] at this
    omega
  have hCls : #Cls = s ^ 2 - if IsLast Q then 1 else 0 := card_class hd D Q
  have hsq := card_sqOf hd Q
  have hA : #(univ.filter fun z : Cell n => sqOf hd z = Q) ≤ #A + if IsLast Q then 1 else 0 := by
    split_ifs with hQ
    · refine (card_le_card (t := insert (blank D) A) ?_).trans (card_insert_le _ _)
      intro z hz
      simp only [A, mem_filter, mem_univ, true_and, mem_insert] at hz ⊢
      by_cases hzb : z = blank D
      · exact Or.inl hzb
      · exact Or.inr ⟨hz, val_ne_zero_of_ne_blank hzb⟩
    · refine card_le_card fun z hz => ?_
      simp only [A, mem_filter, mem_univ, true_and] at hz ⊢
      refine ⟨hz, val_ne_zero_of_ne_blank fun hzb => hQ ?_⟩
      rw [← hz, hzb]
      exact hb
  split_ifs at hCls hA <;> omega

/-- Two distinct cells of a square, avoiding two given cells. -/
theorem exists_two_in_square (hd : HDims n k s) (Q : Sq k) (a b : Cell n) :
    ∃ u u', u ≠ u' ∧ sqOf hd u = Q ∧ sqOf hd u' = Q ∧ u ≠ a ∧ u ≠ b ∧ u' ≠ a ∧ u' ≠ b := by
  let F := univ.filter fun z : Cell n => sqOf hd z = Q ∧ z ≠ a ∧ z ≠ b
  have hsub : (univ.filter fun z : Cell n => sqOf hd z = Q) ⊆ insert a (insert b F) := by
    intro z hz
    simp only [F, mem_filter, mem_univ, true_and, mem_insert] at hz ⊢
    tauto
  have h1 := (card_le_card hsub).trans ((card_insert_le _ _).trans
    (Nat.add_le_add_right (card_insert_le _ _) 1))
  rw [card_sqOf hd Q] at h1
  have hs : 4 ≤ s := by have := hd.room; omega
  have : 16 ≤ s ^ 2 := by nlinarith
  obtain ⟨u, hu, u', hu', hne⟩ := one_lt_card.mp (show 1 < #F by omega)
  simp only [F, mem_filter, mem_univ, true_and] at hu hu'
  exact ⟨u, u', hne, hu.1, hu'.1, hu.2.1, hu.2.2, hu'.2.1, hu'.2.2⟩

theorem four_le_n (hd : HDims n k s) : 4 ≤ n := by
  rw [← hd.mul]
  have := hd.room
  have := hd.two_le
  nlinarith

theorem six_le_n (hd : HDims n k s) : 6 ≤ n := by
  rw [← hd.mul]
  have := hd.room
  have := hd.two_le
  nlinarith

/-- Cells outside a set of cells whose tiles are unchanged keep their status;
if the misplaced cells of `C` lie among those of `D` minus two of them, the
count drops by two. -/
theorem misplaced_drop_two (hd : HDims n k s) {C D : Board n} (a b : Cell n) (hab : a ≠ b)
    (ha : Mis hd D a) (hb : Mis hd D b)
    (hsub : ∀ x, Mis hd C x → Mis hd D x ∧ x ≠ a ∧ x ≠ b) :
    misplaced hd C + 2 ≤ misplaced hd D := by
  rw [misplaced_eq, misplaced_eq]
  have hs : (univ.filter fun x => Mis hd C x) ⊆
      ((univ.filter fun x => Mis hd D x).erase a).erase b := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨h1, h2, h3⟩ := hsub x hx
    simp only [mem_erase, mem_filter, mem_univ, true_and]
    exact ⟨h3, h2, h1⟩
  have hbm : b ∈ (univ.filter fun x => Mis hd D x).erase a := by
    simp only [mem_erase, mem_filter, mem_univ, true_and]
    exact ⟨Ne.symm hab, hb⟩
  have ham : a ∈ univ.filter fun x => Mis hd D x := by
    simp only [mem_filter, mem_univ, true_and]; exact ha
  have h1 := card_le_card hs
  rw [card_erase_of_mem hbm, card_erase_of_mem ham] at h1
  have h2 : 2 ≤ #(univ.filter fun x => Mis hd D x) := by
    have := card_pos.mpr ⟨b, hbm⟩
    rw [card_erase_of_mem ham] at this
    omega
  omega

/-- Four misplaced cells leaving the misplaced set lower the count by four. -/
theorem misplaced_drop_four (hd : HDims n k s) {C D : Board n} (a b c d : Cell n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : Mis hd D a) (hb : Mis hd D b) (hc : Mis hd D c) (hdd : Mis hd D d)
    (hsub : ∀ x, Mis hd C x → Mis hd D x ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d) :
    misplaced hd C + 4 ≤ misplaced hd D := by
  rw [misplaced_eq, misplaced_eq]
  set M := univ.filter fun x => Mis hd D x
  have hs : (univ.filter fun x => Mis hd C x) ⊆ (((M.erase a).erase b).erase c).erase d := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hsub x hx
    simp only [M, mem_erase, mem_filter, mem_univ, true_and]
    exact ⟨h5, h4, h3, h2, h1⟩
  have ham : a ∈ M := by simp only [M, mem_filter, mem_univ, true_and]; exact ha
  have hbm : b ∈ M.erase a := by
    simp only [M, mem_erase, mem_filter, mem_univ, true_and]; exact ⟨Ne.symm hab, hb⟩
  have hcm : c ∈ (M.erase a).erase b := by
    simp only [M, mem_erase, mem_filter, mem_univ, true_and]
    exact ⟨Ne.symm hbc, Ne.symm hac, hc⟩
  have hdm : d ∈ ((M.erase a).erase b).erase c := by
    simp only [M, mem_erase, mem_filter, mem_univ, true_and]
    exact ⟨Ne.symm hcd, Ne.symm hbd, Ne.symm had, hdd⟩
  have h1 := card_le_card hs
  have h2 := card_pos.mpr ⟨d, hdm⟩
  rw [card_erase_of_mem hdm] at h1
  rw [card_erase_of_mem hcm, card_erase_of_mem hbm, card_erase_of_mem ham] at h1 h2
  omega

/-- A misplaced tile `x1`, a wrong tile `x2` of its home square whose home is not
the square of `x1`, and a wrong tile `x3` of that home: one three-cycle fixes
`x1` and `x2`. -/
theorem cleanup_cycle (hd : HDims n k s) [NeZero n] (D : Board n) (x1 x2 x3 : Cell n)
    (hx1 : Mis hd D x1) (hx2Q : sqOf hd x2 = classOf hd (D x1)) (hx2 : Mis hd D x2)
    (hback : classOf hd (D x2) ≠ sqOf hd x1) (hx3Q : sqOf hd x3 = classOf hd (D x2))
    (hx3 : Mis hd D x3) :
    ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧ p.length ≤ 52 * n ∧
      misplaced hd C + 2 ≤ misplaced hd D := by
  have hx12 : x1 ≠ x2 := fun h => hx1.2 (hx2Q.symm.trans (by rw [h]))
  have hx23 : x2 ≠ x3 := fun h => hx2.2 (hx3Q.symm.trans (by rw [h]))
  have hx13 : x1 ≠ x3 := fun h => hback (hx3Q.symm.trans (by rw [h]))
  obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hfix⟩ := exists_three_cycle_sharp D (six_le_n hd)
    x2 x1 x3 hx12.symm hx23 hx13
    (fun h => hx2.1 (by rw [h]; rfl)) (fun h => hx1.1 (by rw [h]; rfl))
    (fun h => hx3.1 (by rw [h]; rfl))
  refine ⟨C, p, hbC, hp, ?_⟩
  refine misplaced_drop_two hd x2 x3 hx23 hx2 hx3 fun x hx => ?_
  have hxx2 : x ≠ x2 := by
    rintro rfl
    apply hx.2
    rw [hCa, hx2Q]
  have hxx3 : x ≠ x3 := by
    rintro rfl
    apply hx.2
    rw [hCc, hx3Q]
  refine ⟨?_, hxx2, hxx3⟩
  by_cases hxx1 : x = x1
  · subst hxx1; exact hx1
  · unfold Mis at hx ⊢
    rwa [hfix x hxx2 hxx1 hxx3] at hx

/-- Two pairs of misplaced tiles, each belonging in the other's square: one
double swap fixes all four. -/
theorem cleanup_swap4 (hd : HDims n k s) [NeZero n] (D : Board n) (x1 x2 y1 y2 : Cell n)
    (hx1 : Mis hd D x1) (hx2 : Mis hd D x2) (hy1 : Mis hd D y1) (hy2 : Mis hd D y2)
    (hx2Q : sqOf hd x2 = classOf hd (D x1)) (hx1Q : sqOf hd x1 = classOf hd (D x2))
    (hy2Q : sqOf hd y2 = classOf hd (D y1)) (hy1Q : sqOf hd y1 = classOf hd (D y2))
    (h1 : x1 ≠ y1) (h2 : x1 ≠ y2) (h3 : x2 ≠ y1) (h4 : x2 ≠ y2) :
    ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧ p.length ≤ 104 * n ∧
      misplaced hd C + 4 ≤ misplaced hd D := by
  have hx12 : x1 ≠ x2 := fun h => hx1.2 (hx2Q.symm.trans (by rw [h]))
  have hy12 : y1 ≠ y2 := fun h => hy1.2 (hy2Q.symm.trans (by rw [h]))
  obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hCd, hfix⟩ := exists_double_swap_sharp D (six_le_n hd)
    x1 y1 x2 y2 h1 hx12 h2 h3.symm hy12 h4
    (fun h => hx1.1 (by rw [h]; rfl)) (fun h => hy1.1 (by rw [h]; rfl))
    (fun h => hx2.1 (by rw [h]; rfl)) (fun h => hy2.1 (by rw [h]; rfl))
  refine ⟨C, p, hbC, hp, ?_⟩
  refine misplaced_drop_four hd x1 y1 x2 y2 h1 hx12 h2 h3.symm hy12 h4 hx1 hy1 hx2 hy2
    fun x hx => ?_
  have e1 : x ≠ x1 := by rintro rfl; exact hx.2 (by rw [hCa, hx1Q])
  have e2 : x ≠ y1 := by rintro rfl; exact hx.2 (by rw [hCb, hy1Q])
  have e3 : x ≠ x2 := by rintro rfl; exact hx.2 (by rw [hCc, hx2Q])
  have e4 : x ≠ y2 := by rintro rfl; exact hx.2 (by rw [hCd, hy2Q])
  refine ⟨?_, e1, e2, e3, e4⟩
  unfold Mis at hx ⊢
  rwa [hfix x e1 e2 e3 e4] at hx

/-- With at least three misplaced tiles, a three-cycle fixes two of them or a
double swap fixes four: cleanup pays `26n` per tile. -/
theorem exists_cleanup_step_big (hd : HDims n k s) [NeZero n] (D : Board n)
    (hb : IsLast (sqOf hd (blank D))) (hm : 3 ≤ misplaced hd D) :
    ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧
      p.length + 26 * n * misplaced hd C ≤ 26 * n * misplaced hd D ∧
      misplaced hd C < misplaced hd D := by
  -- the two bookkeeping forms of a step
  have of2 : ∀ C : Board n, ∀ p : Path D C, blank C = blank D → p.length ≤ 52 * n →
      misplaced hd C + 2 ≤ misplaced hd D →
      ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧
        p.length + 26 * n * misplaced hd C ≤ 26 * n * misplaced hd D ∧
        misplaced hd C < misplaced hd D := by
    intro C p hbC hp hdrop
    refine ⟨C, p, hbC, ?_, by omega⟩
    have := Nat.mul_le_mul_left (26 * n) hdrop
    nlinarith
  have of4 : ∀ C : Board n, ∀ p : Path D C, blank C = blank D → p.length ≤ 104 * n →
      misplaced hd C + 4 ≤ misplaced hd D →
      ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧
        p.length + 26 * n * misplaced hd C ≤ 26 * n * misplaced hd D ∧
        misplaced hd C < misplaced hd D := by
    intro C p hbC hp hdrop
    refine ⟨C, p, hbC, ?_, by omega⟩
    have := Nat.mul_le_mul_left (26 * n) hdrop
    nlinarith
  -- a wrong tile of the home square of any misplaced tile
  have wrong : ∀ x, Mis hd D x → ∃ x', sqOf hd x' = classOf hd (D x) ∧ Mis hd D x' := by
    intro x hx
    obtain ⟨x', h1, h2, h3⟩ := exists_wrong_in_square hd D hb x hx.1 hx.2
    exact ⟨x', h1, h2, by rw [h1]; exact h3⟩
  -- the three-cycle from a misplaced tile whose home's wrong tile leads elsewhere
  have cyc : ∀ x1 x2, Mis hd D x1 → sqOf hd x2 = classOf hd (D x1) → Mis hd D x2 →
      classOf hd (D x2) ≠ sqOf hd x1 →
      ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧
        p.length + 26 * n * misplaced hd C ≤ 26 * n * misplaced hd D ∧
        misplaced hd C < misplaced hd D := by
    intro x1 x2 hx1 hx2Q hx2 hback
    obtain ⟨x3, hx3Q, hx3⟩ := wrong x2 hx2
    obtain ⟨C, p, hbC, hp, hdrop⟩ := cleanup_cycle hd D x1 x2 x3 hx1 hx2Q hx2 hback hx3Q hx3
    exact of2 C p hbC hp hdrop
  obtain ⟨x1, hx1⟩ : ∃ x1, Mis hd D x1 := by
    by_contra hno
    push Not at hno
    have : misplaced hd D = 0 := by
      rw [misplaced_eq, card_eq_zero, filter_eq_empty_iff]
      exact fun x _ => hno x
    omega
  obtain ⟨x2, hx2Q, hx2⟩ := wrong x1 hx1
  by_cases hback : classOf hd (D x2) = sqOf hd x1
  swap
  · exact cyc x1 x2 hx1 hx2Q hx2 hback
  have hx12 : x1 ≠ x2 := fun h => hx1.2 (hx2Q.symm.trans (by rw [h]))
  -- a third misplaced tile
  obtain ⟨y, hy, hyx1, hyx2⟩ : ∃ y, Mis hd D y ∧ y ≠ x1 ∧ y ≠ x2 := by
    by_contra hno
    push Not at hno
    have hsub : (univ.filter fun x => Mis hd D x) ⊆ {x1, x2} := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      simp only [mem_insert, mem_singleton]
      by_contra hc
      push Not at hc
      exact hc.2 (hno x hx hc.1)
    have := card_le_card hsub
    rw [← misplaced_eq] at this
    have := card_insert_le x1 ({x2} : Finset (Cell n))
    simp only [card_singleton] at this
    omega
  obtain ⟨y2, hy2Q, hy2⟩ := wrong y hy
  by_cases hback2 : classOf hd (D y2) = sqOf hd y
  swap
  · exact cyc y y2 hy hy2Q hy2 hback2
  have hx1ne : sqOf hd x2 ≠ sqOf hd x1 := by rw [hx2Q]; exact hx1.2
  by_cases hy2x1 : y2 = x1
  · -- `y` lies in `x2`'s square and belongs to `x1`'s square
    have hyA : sqOf hd x1 = classOf hd (D y) := by rw [← hy2x1]; exact hy2Q
    have hyB : classOf hd (D x1) = sqOf hd y := by rw [← hy2x1]; exact hback2
    -- two tiles of class `sqOf x1` (`x2` and `y`) lie outside it
    obtain ⟨x1', hx1'Q, hx1'0, hx1'c, hx1'x1⟩ := exists_wrong_in_square_ne hd D hb x2 y x1
      (Ne.symm hyx2) hx2.1 hx2.2 hy.1 hy.2 (by rw [← hyA, hback])
    have hx1' : Mis hd D x1' := ⟨hx1'0, by rw [hx1'Q]; exact hx1'c⟩
    have hsqx1' : sqOf hd x1' = sqOf hd x1 := by rw [hx1'Q, hback]
    have hx2x1' : x2 ≠ x1' := fun e => hx1ne (by rw [e, hsqx1'])
    obtain ⟨x2', hx2'Q, hx2'⟩ := wrong x1' hx1'
    by_cases hback3 : classOf hd (D x2') = sqOf hd x1'
    swap
    · exact cyc x1' x2' hx1' hx2'Q hx2' hback3
    by_cases hx2'x2 : x2' = x2
    · -- pair `x1'` with `y`
      have e1 : sqOf hd y = classOf hd (D x1') := by
        rw [← hyB, ← hx2Q, ← hx2'x2, hx2'Q]
      obtain ⟨C, p, hbC, hp, hdrop⟩ := cleanup_swap4 hd D x1 x2 x1' y hx1 hx2 hx1' hy hx2Q
        hback.symm e1 (by rw [hsqx1', hyA]) (Ne.symm hx1'x1) (Ne.symm hyx1) hx2x1' (Ne.symm hyx2)
      exact of4 C p hbC hp hdrop
    · have hx2'x1 : x2' ≠ x1 := fun e => hx1'.2 (by rw [← hx2'Q, e, hsqx1'])
      obtain ⟨C, p, hbC, hp, hdrop⟩ := cleanup_swap4 hd D x1 x2 x1' x2' hx1 hx2 hx1' hx2' hx2Q
        hback.symm hx2'Q hback3.symm (Ne.symm hx1'x1) (Ne.symm hx2'x1) hx2x1' (Ne.symm hx2'x2)
      exact of4 C p hbC hp hdrop
  by_cases hy2x2 : y2 = x2
  · -- `y` lies in `x1`'s square and belongs to `x2`'s square
    have hyc : classOf hd (D y) = classOf hd (D x1) := by rw [← hy2Q, hy2x2, hx2Q]
    have hsqy : sqOf hd y = sqOf hd x1 := by rw [← hback2, hy2x2, hback]
    obtain ⟨x2'', hx2''Q, hx2''0, hx2''c, hx2''x2⟩ := exists_wrong_in_square_ne hd D hb x1 y x2
      (Ne.symm hyx1) hx1.1 hx1.2 hy.1 hy.2 hyc
    have hx2'' : Mis hd D x2'' := ⟨hx2''0, by rw [hx2''Q]; exact hx2''c⟩
    have hx2''y : sqOf hd x2'' = classOf hd (D y) := by rw [hx2''Q, hyc]
    have hx1x2'' : x1 ≠ x2'' := fun e => hx1.2 (by rw [← hx2''Q, ← e])
    by_cases hback4 : classOf hd (D x2'') = sqOf hd y
    · obtain ⟨C, p, hbC, hp, hdrop⟩ := cleanup_swap4 hd D x1 x2 y x2'' hx1 hx2 hy hx2'' hx2Q
        hback.symm hx2''y hback4.symm (Ne.symm hyx1) hx1x2'' (Ne.symm hyx2) (Ne.symm hx2''x2)
      exact of4 C p hbC hp hdrop
    · exact cyc y x2'' hy hx2''y hx2'' hback4
  -- a second, disjoint pair
  have hyy2 : y ≠ y2 := fun h => hy.2 (hy2Q.symm.trans (by rw [h]))
  obtain ⟨C, p, hbC, hp, hdrop⟩ := cleanup_swap4 hd D x1 x2 y y2 hx1 hx2 hy hy2 hx2Q hback.symm
    hy2Q hback2.symm (Ne.symm hyx1) (Ne.symm hy2x1) (Ne.symm hyx2) (Ne.symm hy2x2)
  exact of4 C p hbC hp hdrop

/-- One three-cycle or double swap removes at least two misplaced tiles, keeping
the blank. -/
theorem exists_cleanup_step (hd : HDims n k s) [NeZero n] (D : Board n)
    (hb : IsLast (sqOf hd (blank D))) (hm : misplaced hd D ≠ 0) :
    ∃ C : Board n, ∃ p : Path D C, blank C = blank D ∧ p.length ≤ 104 * n ∧
      misplaced hd C + 2 ≤ misplaced hd D := by
  obtain ⟨x1, hx1⟩ : ∃ x1, Mis hd D x1 := by
    by_contra hno
    push Not at hno
    apply hm
    rw [misplaced_eq, card_eq_zero, filter_eq_empty_iff]
    exact fun x _ => hno x
  obtain ⟨x2, hx2Q, hx2z, hx2c⟩ := exists_wrong_in_square hd D hb x1 hx1.1 hx1.2
  have hx2 : Mis hd D x2 := ⟨hx2z, by rw [hx2Q]; exact hx2c⟩
  have hx12 : x1 ≠ x2 := fun h => hx1.2 (hx2Q.symm.trans (by rw [h]))
  by_cases hback : classOf hd (D x2) = sqOf hd x1
  · -- `x1` and `x2` belong in each other's squares: a double swap fixes both
    obtain ⟨u, u', huu, hu, hu', hux2, hub, hu'x2, hu'b⟩ :=
      exists_two_in_square hd (sqOf hd x2) x2 (blank D)
    have hx1u : x1 ≠ u := fun h => hx1.2 (hx2Q.symm.trans (hu.symm.trans (by rw [h])))
    have hx1u' : x1 ≠ u' := fun h => hx1.2 (hx2Q.symm.trans (hu'.symm.trans (by rw [h])))
    obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hCd, hfix⟩ := exists_double_swap_sharp D (six_le_n hd)
      x1 u x2 u' hx1u hx12 hx1u' hux2 huu hu'x2.symm
      (fun h => hx1.1 (by rw [h]; rfl)) (fun h => val_ne_zero_of_ne_blank hub (by rw [h]; rfl))
      (fun h => hx2z (by rw [h]; rfl)) (fun h => val_ne_zero_of_ne_blank hu'b (by rw [h]; rfl))
    refine ⟨C, p, hbC, hp, ?_⟩
    -- the misplaced cells of `C`, moved by the swap `u ↔ u'`, lie among those of `D`
    have hsub : (univ.filter fun x => Mis hd C x) ⊆
        ((((univ.filter fun x => Mis hd D x).image (Equiv.swap u u')).erase x2).erase x1) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      simp only [mem_erase, mem_image]
      have hxx2 : x ≠ x2 := by
        rintro rfl
        apply hx.2
        rw [hCc, hx2Q]
      have hxx1 : x ≠ x1 := by
        rintro rfl
        apply hx.2
        rw [hCa, hback]
      refine ⟨hxx1, hxx2, Equiv.swap u u' x, ?_, Equiv.swap_apply_self _ _ _⟩
      simp only [mem_filter, mem_univ, true_and]
      by_cases hxb : x = u
      · subst hxb
        rw [Equiv.swap_apply_left]
        unfold Mis at hx ⊢
        rw [hCb] at hx
        rwa [hu', ← hu]
      by_cases hxd : x = u'
      · subst hxd
        rw [Equiv.swap_apply_right]
        unfold Mis at hx ⊢
        rw [hCd] at hx
        rwa [hu, ← hu']
      rw [Equiv.swap_apply_of_ne_of_ne hxb hxd]
      unfold Mis at hx ⊢
      rwa [hfix x hxx1 hxb hxx2 hxd] at hx
    have hmem2 : x2 ∈ (univ.filter fun x => Mis hd D x).image (Equiv.swap u u') := by
      rw [mem_image]
      exact ⟨x2, by simpa using hx2, Equiv.swap_apply_of_ne_of_ne (Ne.symm hux2) (Ne.symm hu'x2)⟩
    have hmem1 : x1 ∈ ((univ.filter fun x => Mis hd D x).image (Equiv.swap u u')).erase x2 := by
      rw [mem_erase, mem_image]
      exact ⟨hx12, x1, by simpa using hx1, Equiv.swap_apply_of_ne_of_ne hx1u hx1u'⟩
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hmem1, card_erase_of_mem hmem2] at h1
    have h2 := card_image_le (s := univ.filter fun x => Mis hd D x) (f := Equiv.swap u u')
    have h3 : 1 ≤ #(((univ.filter fun x => Mis hd D x).image (Equiv.swap u u')).erase x2) :=
      card_pos.mpr ⟨x1, hmem1⟩
    rw [card_erase_of_mem hmem2] at h3
    rw [misplaced_eq, misplaced_eq]
    omega
  · -- a third misplaced tile in the home square of `x2`: one three-cycle fixes two
    obtain ⟨x3, hx3Q, hx3z, hx3c⟩ := exists_wrong_in_square hd D hb x2 hx2z hx2.2
    have hx3 : Mis hd D x3 := ⟨hx3z, by rw [hx3Q]; exact hx3c⟩
    have hx23 : x2 ≠ x3 := fun h => hx2.2 (hx3Q.symm.trans (by rw [h]))
    have hx13 : x1 ≠ x3 := fun h => hback (hx3Q.symm.trans (by rw [h]))
    obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hfix⟩ := exists_three_cycle_sharp D (six_le_n hd)
      x2 x1 x3 hx12.symm hx23 hx13
      (fun h => hx2z (by rw [h]; rfl)) (fun h => hx1.1 (by rw [h]; rfl))
      (fun h => hx3z (by rw [h]; rfl))
    refine ⟨C, p, hbC, by omega, ?_⟩
    refine misplaced_drop_two hd x2 x3 hx23 hx2 hx3 fun x hx => ?_
    have hxx2 : x ≠ x2 := by
      rintro rfl
      apply hx.2
      rw [hCa, hx2Q]
    have hxx3 : x ≠ x3 := by
      rintro rfl
      apply hx.2
      rw [hCc, hx3Q]
    refine ⟨?_, hxx2, hxx3⟩
    by_cases hxx1 : x = x1
    · subst hxx1; exact hx1
    · unfold Mis at hx ⊢
      rwa [hfix x hxx2 hxx1 hxx3] at hx

/-- Cleanup steps until nothing is misplaced: `26n` per tile and one final
double swap. -/
theorem exists_cleanup_loop (hd : HDims n k s) [NeZero n] :
    ∀ m (D : Board n), misplaced hd D = m → IsLast (sqOf hd (blank D)) →
      ∃ C : Board n, ∃ p : Path D C,
        (∀ x, (C x).val ≠ 0 → classOf hd (C x) = sqOf hd x) ∧ IsLast (sqOf hd (blank C)) ∧
        p.length ≤ 26 * n * m + 104 * n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D hm hb
    by_cases h0 : m = 0
    · subst h0
      exact ⟨D, Path.nil D, sorted_of_misplaced_zero hd hm, hb, by simp⟩
    by_cases h3 : 3 ≤ m
    · obtain ⟨E, p, hbE, hp, hlt⟩ := exists_cleanup_step_big hd D hb (hm ▸ h3)
      obtain ⟨C, q, hC, hbC, hq⟩ := ih (misplaced hd E) (hm ▸ hlt) E rfl (hbE ▸ hb)
      refine ⟨C, p.append q, hC, hbC, ?_⟩
      rw [Path.length_append]
      rw [hm] at hp
      omega
    · obtain ⟨E, p, hbE, hp, hlt⟩ := exists_cleanup_step hd D hb (hm ▸ h0)
      have hE : misplaced hd E = 0 := by omega
      refine ⟨E, p, sorted_of_misplaced_zero hd hE, hbE ▸ hb, ?_⟩
      have : 0 ≤ 26 * n * m := Nat.zero_le _
      omega

end CleanupAux

open CleanupAux LayoutFacts

/-- Sort every tile into its own square. The length is bounded: the cleanup is
followed by Finish, and the two together end at the target, so only half of
their moves are inefficient. -/
theorem exists_cleanup (hd : HDims n k s) [NeZero n] (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      (∀ x, (C x).val ≠ 0 → classOf hd (C x) = sqOf hd x) ∧ IsLast (sqOf hd (blank C)) ∧
      p.length ≤ 26 * n * (misplaced hd B + 2 * n + 5) := by
  obtain ⟨D, p, hD, hp, -⟩ := exists_blank_access_path_preserving B (blank (target n))
  have hpn : p.length ≤ 2 * n := by
    refine hp.trans ?_
    have := (blank B).1.isLt
    have := (blank B).2.isLt
    have := (blank (target n)).1.isLt
    have := (blank (target n)).2.isLt
    simp only [gridDistance, Nat.dist]
    omega
  have hbD : IsLast (sqOf hd (blank D)) := by
    rw [hD, isLast_iff hd]
  have hmD := misplaced_path hd p
  obtain ⟨C, q, hC, hbC, hq⟩ := exists_cleanup_loop hd _ D rfl hbD
  refine ⟨C, p.append q, hC, hbC, ?_⟩
  rw [Path.length_append]
  set m := misplaced hd B
  have h1 : 26 * n * misplaced hd D ≤ 26 * n * (m + 2 * n) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : 26 * n * (m + 2 * n + 5) = 26 * n * (m + 2 * n) + 130 * n := by ring
  omega

end SlidingPuzzle.Hub
