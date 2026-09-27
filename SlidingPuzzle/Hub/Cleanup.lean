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

/-- Cleanup steps until nothing is misplaced. -/
theorem exists_cleanup_loop (hd : HDims n k s) [NeZero n] :
    ∀ m (D : Board n), misplaced hd D = m → IsLast (sqOf hd (blank D)) →
      ∃ C : Board n, ∃ p : Path D C,
        (∀ x, (C x).val ≠ 0 → classOf hd (C x) = sqOf hd x) ∧ IsLast (sqOf hd (blank C)) ∧
        p.length ≤ 52 * n * (m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D hm hb
    by_cases h0 : m = 0
    · subst h0
      exact ⟨D, Path.nil D, sorted_of_misplaced_zero hd hm, hb, by simp⟩
    obtain ⟨E, p, hbE, hp, hlt⟩ := exists_cleanup_step hd D hb (hm ▸ h0)
    obtain ⟨C, q, hC, hbC, hq⟩ := ih (misplaced hd E) (by omega) E rfl (hbE ▸ hb)
    refine ⟨C, p.append q, hC, hbC, ?_⟩
    rw [Path.length_append]
    have : 52 * n * (misplaced hd E + 1) + 104 * n ≤ 52 * n * (m + 1) := by
      have := Nat.mul_le_mul_left (52 * n) (show misplaced hd E + 1 + 2 ≤ m + 1 by omega)
      nlinarith
    omega

end CleanupAux

open CleanupAux LayoutFacts

/-- Sort every tile into its own square. -/
theorem exists_cleanup (hd : HDims n k s) [NeZero n] (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      (∀ x, (C x).val ≠ 0 → classOf hd (C x) = sqOf hd x) ∧ IsLast (sqOf hd (blank C)) ∧
      p.inefficientMoves ≤ 52 * n * (misplaced hd B + 2 * n + 2) := by
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
  refine (Path.inefficientMoves_le_length _).trans ?_
  rw [Path.length_append]
  set m := misplaced hd B
  have h1 : 52 * n * (misplaced hd D + 1) ≤ 52 * n * (m + 2 * n + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : 52 * n * (m + 2 * n + 2) = 52 * n * (m + 2 * n + 1) + 52 * n := by ring
  have h3 : 2 * n ≤ 52 * n := by omega
  omega

end SlidingPuzzle.Hub
