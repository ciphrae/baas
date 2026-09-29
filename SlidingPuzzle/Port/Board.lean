import SlidingPuzzle.Port.RunMain
import SlidingPuzzle.Port.Simulate

/-! # The port abstraction of a board

`absPState B pt` reads a board whose blank lies in the box of port `pt` of its square.
It realizes the board (`prel_absPState`), extends the tree abstraction, and every
port holds at least `σ²` cells (`psz_ge`). -/
namespace SlidingPuzzle.Port
open Finset
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf reservoir)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

theorem reservoir_of_inBoxOf (pd : PDims n k s q σ) {Q : Sq k} {pt : Pt} {x : Cell n}
    (h : InBoxOf s σ Q pt x) : reservoir k s Q x := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb := box_bounds pd pt
  rw [inBox_iff (by have := pd.fit; omega)] at h3
  exact ⟨h1, h2, by omega, by omega⟩

/-- The port abstraction of a board. -/
noncomputable def absPState (pd : PDims n k s q σ) (B : Board n) (pt : Pt) : PState k q where
  row := (absState L pd.hd B).row
  col := (absState L pd.hd B).col
  cnt := regionCount L pd.hd B
  pc := fun Q p y => pcount L s σ pd.hd B Q (some p) y
  blank := sqOf pd.hd (blank B)
  bp := pt

theorem absPState_toI (pd : PDims n k s q σ) (B : Board n) (pt : Pt) :
    (absPState L pd B pt).toI = absState L pd.hd B := rfl

theorem prel_absPState (pd : PDims n k s q σ) (B : Board n) {pt : Pt}
    (hb : InBoxOf s σ (sqOf pd.hd (blank B)) pt (blank B)) :
    PRel L pd B (absPState L pd B pt) := by
  have hr := reservoir_of_inBoxOf pd hb
  have hR := rel_absState L pd.td B hr
  exact ⟨hR.1, hR.2.1, fun _ _ => rfl, fun _ _ _ => rfl, hb⟩

/-- A realized port state is realized as a tree state. -/
theorem rel_of_prel (pd : PDims n k s q σ) {B : Board n} {ρ : PState k q} (h : PRel L pd B ρ) :
    Rel L pd.hd B ρ.toI :=
  ⟨h.1, h.2.1, h.2.2.1, reservoir_of_inBoxOf pd h.2.2.2.2⟩

theorem sum_pc_le (pd : PDims n k s q σ) (B : Board n) (pt0 : Pt) (Q y : Sq k) :
    ∑ pt, (absPState L pd B pt0).pc Q pt y ≤ (absPState L pd B pt0).cnt Q y := by
  show ∑ pt, pcount L s σ pd.hd B Q (some pt) y ≤ regionCount L pd.hd B Q y
  rw [regionCount_eq_sum L (σ := σ), Fintype.sum_option]
  omega

/-- Every port has at least `σ²` cells. -/
theorem psz_ge (pd : PDims n k s q σ) (B : Board n) {pt0 : Pt}
    (hb : InBoxOf s σ (sqOf pd.hd (blank B)) pt0 (blank B)) (Q : Sq k) (pt : Pt) :
    σ ^ 2 ≤ psz (absPState L pd B pt0) Q pt := by
  set a : Option (Sq k × Part) := some (Q, some pt)
  set S := univ.filter fun x : Cell n => rkey L s σ pd.hd x = a with hS
  -- the tiles of the port
  have h1 : ∑ y, pcount L s σ pd.hd B Q (some pt) y = #(S.filter fun x => (B x).val ≠ 0) := by
    rw [card_eq_sum_card_fiberwise (f := fun x => classOf pd.hd (B x)) (t := univ)
      (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun y _ => ?_
    unfold pcount kcount
    rw [hS, filter_filter]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, a]
  have h2 := card_filter_add_card_filter_not (s := S) (fun x => (B x).val ≠ 0)
  -- the blank
  have h3 : #(S.filter fun x => ¬ (B x).val ≠ 0) ≤
      if sqOf pd.hd (blank B) = Q ∧ pt0 = pt then 1 else 0 := by
    have hsub : (S.filter fun x => ¬ (B x).val ≠ 0) ⊆ {blank B} := by
      intro x hx
      simp only [mem_filter, not_not] at hx
      rw [mem_singleton]
      exact SlidingPuzzle.Hub.LayoutFacts.eq_blank_of_val_eq_zero hx.2
    split_ifs with hc
    · exact (card_le_card hsub).trans (by simp)
    · apply le_of_eq
      rw [card_eq_zero, filter_eq_empty_iff]
      intro x hx hv
      have hx' := SlidingPuzzle.Hub.LayoutFacts.eq_blank_of_val_eq_zero (not_not.mp hv)
      simp only [hS, mem_filter, mem_univ, true_and] at hx
      rw [hx', rkey_inBoxOf L pd hb] at hx
      simp only [a, Option.some.injEq, Prod.mk.injEq] at hx
      exact hc ⟨hx.1, hx.2⟩
  -- the box
  have hbb := box_bounds pd pt
  have hσ : σ + 1 ≤ s := by have := pd.fit; omega
  have h4 : σ ^ 2 ≤ #S := by
    set f : ℕ × ℕ → Cell n := fun p => lc s Q (boxR k s σ pt + p.1) (boxC k s σ pt + p.2)
    have hinj : Set.InjOn f ↑(range σ ×ˢ range σ) := by
      intro p hp p' hp' he
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hp hp'
      have := lc_inj pd.hd Q (r := boxR k s σ pt + p.1) (c := boxC k s σ pt + p.2)
        (r' := boxR k s σ pt + p'.1) (c' := boxC k s σ pt + p'.2)
        (by omega) (by omega) (by omega) (by omega) he
      exact Prod.ext (by omega) (by omega)
    have hsub : (range σ ×ˢ range σ).image f ⊆ S := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      simp only [mem_product, mem_range] at hp
      simp only [hS, mem_filter, mem_univ, true_and]
      exact rkey_box L pd Q ((inBox_iff hσ pt _ _).2 ⟨by omega, by omega, by omega, by omega⟩)
    have := card_le_card hsub
    rw [card_image_of_injOn hinj, card_product, card_range] at this
    nlinarith
  show σ ^ 2 ≤ (∑ z, pcount L s σ pd.hd B Q (some pt) z) +
    (if sqOf pd.hd (blank B) = Q ∧ pt0 = pt then 1 else 0)
  omega

end SlidingPuzzle.Port
