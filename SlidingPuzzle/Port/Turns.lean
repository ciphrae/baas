import SlidingPuzzle.Port.ServeChain

/-! # A route turns at most once

Hops of a route keep their side while they stay on one axis (`hop_le`, `hop_ge`), so
consecutive hops on one axis use the same port. The only turning stage is the last
row hop. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

theorem side_hop (J c : Fin k) (h : J ≠ c) (ht : (L.hop J c).2 ≠ c) :
    decide (c < (L.hop J c).2) = decide (c < J) := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have := L.hop_le J c hlt
    have h1 : ¬ c < (L.hop J c).2 := fun h' => absurd (lt_of_le_of_lt this h') (lt_irrefl _)
    have h2 : ¬ c < J := fun h' => absurd (lt_trans hlt h') (lt_irrefl _)
    simp [h1, h2]
  · have := L.hop_ge J c hlt
    have h1 : c < (L.hop J c).2 := lt_of_le_of_ne this (Ne.symm ht)
    simp [h1, hlt]

theorem stage_col {w D : Sq k} (h : w.2 = D.2) :
    L.stage w D = ((true, ⟨w.2, (L.hop w.1 D.1).1, (L.hop w.1 D.1).2, decide (D.1 < w.1)⟩), w.1) := by
  simp [LaneSys.stage, h]

theorem stage_row {w D : Sq k} (h : w.2 ≠ D.2) :
    L.stage w D = ((false, ⟨w.1, (L.hop w.2 D.2).1, (L.hop w.2 D.2).2, decide (D.2 < w.2)⟩), w.2) := by
  simp [LaneSys.stage, h]

theorem nxt_col {w D : Sq k} (h : w.2 = D.2) : L.nxt w D = ((L.hop w.1 D.1).2, w.2) := by
  simp [LaneSys.nxt, stage_col L h, land, colLand]

theorem nxt_row {w D : Sq k} (h : w.2 ≠ D.2) : L.nxt w D = (w.1, (L.hop w.2 D.2).2) := by
  simp [LaneSys.nxt, stage_row L h, land, rowLand]

theorem dport_col {w D : Sq k} (h : w.2 = D.2) :
    dport L w D = if decide (D.1 < w.1) then .bl else .tl := by
  simp [dport, stage_col L h, lport, LaneI.side]

theorem dport_row {w D : Sq k} (h : w.2 ≠ D.2) :
    dport L w D = if decide (D.2 < w.2) then .tr else .tl := by
  simp [dport, stage_row L h, lport, LaneI.side]

/-- The column phase does not turn. -/
theorem tcnt_col (D : Sq k) : ∀ w : Sq k, w.2 = D.2 → tcnt L w D = 0 := by
  intro w
  induction hr : L.srank w D generalizing w with
  | zero => intro _; rw [srank_eq_zero hr, tcnt_self]
  | succ r ih =>
    intro hw
    have hwD : w ≠ D := fun e => by rw [e, srank_self] at hr; omega
    have hrn := srank_nxt (L := L) hwD
    have h1 : w.1 ≠ D.1 := fun e => hwD (Prod.ext e hw)
    have hn2 : (L.nxt w D).2 = D.2 := by rw [nxt_col L hw]; exact hw
    rw [tcnt_cons L hwD, ih (L.nxt w D) (by omega) hn2, if_neg]
    rintro ⟨hne, hp⟩
    apply hp
    have ht : (L.hop w.1 D.1).2 ≠ D.1 := by
      intro e; apply hne; rw [land_stage, nxt_col L hw]; exact Prod.ext e hw
    rw [land_stage, dport_col L hn2, nxt_col L hw, show lport (L.stage w D).1 = dport L w D from rfl,
      dport_col L hw]
    simp only
    rw [side_hop L w.1 D.1 h1 ht]

/-- A route turns at most once. -/
theorem tcnt_le_one (D : Sq k) : ∀ w : Sq k, tcnt L w D ≤ 1 := by
  intro w
  induction hr : L.srank w D generalizing w with
  | zero => rw [srank_eq_zero hr, tcnt_self]; omega
  | succ r ih =>
    have hwD : w ≠ D := fun e => by rw [e, srank_self] at hr; omega
    have hrn := srank_nxt (L := L) hwD
    by_cases hw : w.2 = D.2
    · rw [tcnt_col L D w hw]; omega
    · by_cases ht : (L.hop w.2 D.2).2 = D.2
      · have hn2 : (L.nxt w D).2 = D.2 := by rw [nxt_row L hw]; exact ht
        rw [tcnt_cons L hwD, tcnt_col L D _ hn2]
        split_ifs <;> omega
      · have hn2 : (L.nxt w D).2 ≠ D.2 := by rw [nxt_row L hw]; exact ht
        rw [tcnt_cons L hwD, if_neg]
        · exact ih (L.nxt w D) (by omega)
        rintro ⟨hne, hp⟩
        apply hp
        have h1 : w.2 ≠ D.2 := hw
        rw [land_stage, dport_row L hn2, nxt_row L hw, show lport (L.stage w D).1 = dport L w D from rfl,
          dport_row L hw]
        simp only
        rw [side_hop L w.2 D.2 h1 ht]

end SlidingPuzzle.Port
