import SlidingPuzzle.Tree.Abs
import SlidingPuzzle.Moves.ThreeCycleSharp

/-! # Preloading home tiles

Before the plan is made, every square `Q` gets at least `R Q` tiles of its own
class in its region: while some square lacks them, a three-cycle moves a class-`Q`
tile from outside into a wrong cell of `Q`'s region, that cell's tile onto a lane
cell and the lane cell's tile to where the class-`Q` tile was. Lane cells lie in
no region, so no square loses a home tile. Each step costs at most `52 n` moves. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq sqOf classOf reservoir)

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

/-- Home tiles in the region of `Q`. -/
noncomputable abbrev homeCnt (td : TDims n k s q) (B : Board n) (Q : Sq k) : ℕ :=
  regionCount L td.hd B Q Q

/-- A lane with a positive length exists. -/
theorem exists_lane_pos (td : TDims n k s q) : ∃ H : LaneI k q, 0 < blen L H := by
  have hk := td.hd.two_le
  set J : Fin k := ⟨0, by omega⟩
  set c : Fin k := ⟨1, by omega⟩
  have hJc : J ≠ c := by simp [J, c, Fin.ext_iff]
  have h := L.hop_in J c hJc
  refine ⟨⟨J, (L.hop J c).1, (L.hop J c).2, decide (c < J)⟩, ?_⟩
  unfold blen
  have hd : decide (c < J) = false := by
    simp only [decide_eq_false_iff_not, not_lt]; exact Fin.mk_le_mk.mpr (by omega)
  simp only [hd] at h ⊢
  unfold InPiece at h
  have hJ0 : J.val = 0 := rfl
  simp only [Bool.false_eq_true, if_false] at h
  omega

theorem homeCnt_step (td : TDims n k s q) (B C : Board n) (Q : Sq k) (a b c : Cell n)
    (ha : region L s Q a) (haQ : classOf td.hd (B a) ≠ Q) (hb : ¬ region L s Q b)
    (hbQ : classOf td.hd (B b) = Q) (hb0 : (B b).val ≠ 0) (hc : LaneCell L s c)
    (hCa : C a = B b) (hfix : ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x) :
    (∀ Q', homeCnt L td B Q' ≤ homeCnt L td C Q') ∧ homeCnt L td B Q + 1 ≤ homeCnt L td C Q := by
  classical
  have hsub : ∀ Q', (univ.filter fun x : Cell n =>
      region L s Q' x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q') ⊆
      (univ.filter fun x : Cell n => region L s Q' x ∧ (C x).val ≠ 0 ∧ classOf td.hd (C x) = Q') := by
    intro Q' x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨hr, h0, hcl⟩ := hx
    have hxa : x ≠ a := by
      rintro rfl
      have := region_sqOf L td.hd hr
      rw [region_sqOf L td.hd ha] at this
      exact haQ (hcl.trans this.symm)
    have hxb : x ≠ b := by
      rintro rfl
      have e := region_sqOf L td.hd hr
      rw [hbQ] at hcl
      subst hcl
      exact hb hr
    have hxc : x ≠ c := by
      rintro rfl; exact hr.2.2 hc
    rw [hfix x hxa hxb hxc]
    exact ⟨hr, h0, hcl⟩
  refine ⟨fun Q' => card_le_card (hsub Q'), ?_⟩
  have hanot : a ∉ (univ.filter fun x : Cell n =>
      region L s Q x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q) := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro _ _ h; exact haQ h
  have hain : a ∈ (univ.filter fun x : Cell n =>
      region L s Q x ∧ (C x).val ≠ 0 ∧ classOf td.hd (C x) = Q) := by
    simp only [mem_filter, mem_univ, true_and]
    rw [hCa]; exact ⟨ha, hb0, hbQ⟩
  have := card_lt_card (Finset.ssubset_iff_of_subset (hsub Q) |>.mpr ⟨a, hain, hanot⟩)
  show regionCount L td.hd B Q Q + 1 ≤ regionCount L td.hd C Q Q
  unfold regionCount
  omega

/-- The total deficit of home tiles. -/
noncomputable def deficit (td : TDims n k s q) (R : Sq k → ℕ) (B : Board n) : ℕ :=
  ∑ Q, (R Q - homeCnt L td B Q)

theorem exists_wrong_cell (td : TDims n k s q) (B : Board n) (Q : Sq k) (R : ℕ)
    (hR : R + 2 ≤ (s - q) * (s - q)) (hlt : homeCnt L td B Q < R) :
    ∃ a, region L s Q a ∧ (B a).val ≠ 0 ∧ classOf td.hd (B a) ≠ Q := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (univ.filter fun x : Cell n => region L s Q x) ⊆
      insert (blank B) (univ.filter fun x : Cell n =>
        region L s Q x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_insert, mem_filter, mem_univ, true_and]
    by_cases h0 : (B x).val = 0
    · left; exact Hub.LayoutFacts.eq_blank_of_val_eq_zero h0
    · right; exact ⟨hx, h0, hne x hx h0⟩
  have h1 := card_le_card hsub
  have h2 := card_insert_le (blank B) (univ.filter fun x : Cell n =>
    region L s Q x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q)
  have h3 := regionSize_ge (n := n) L td Q
  unfold regionSize at h3
  have : homeCnt L td B Q = (univ.filter fun x : Cell n =>
      region L s Q x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q).card := rfl
  omega

theorem exists_home_outside (td : TDims n k s q) (B : Board n) (Q : Sq k) (R : ℕ)
    (hR : R + 2 ≤ s ^ 2) (hlt : homeCnt L td B Q < R) :
    ∃ b, ¬ region L s Q b ∧ (B b).val ≠ 0 ∧ classOf td.hd (B b) = Q := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (univ.filter fun x : Cell n => (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q) ⊆
      (univ.filter fun x : Cell n => region L s Q x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    by_contra hr
    exact hne x (fun h => hr ⟨h, hx⟩) hx.1 hx.2
  have h1 := card_le_card hsub
  rw [Hub.LayoutFacts.card_class td.hd B Q] at h1
  have : homeCnt L td B Q = (univ.filter fun x : Cell n =>
      region L s Q x ∧ (B x).val ≠ 0 ∧ classOf td.hd (B x) = Q).card := rfl
  split_ifs at h1 <;> omega

theorem exists_lane_cell (td : TDims n k s q) (B : Board n)
    (hb : reservoir k s (sqOf td.hd (blank B)) (blank B)) (b : Cell n) :
    ∃ c, LaneCell L s c ∧ (B c).val ≠ 0 ∧ c ≠ b := by
  obtain ⟨H, hH⟩ := exists_lane_pos L td
  have hs := td.s_pos
  have hks := td.k_lt_s
  have hlen : 1 < rowLen L s H := by
    unfold rowLen; have := Nat.mul_le_mul_right s hH; have := td.hd.room; omega
  by_cases h0 : rowCell (n := n) s H 0 = b
  · refine ⟨rowCell s H 1, rowCell_lane L td H 1 hlen, rowCell_nonblank L td hb H hlen, ?_⟩
    rw [← h0]; intro e
    have := (rowCell_inj L td hlen (by omega) e).2; omega
  · exact ⟨rowCell s H 0, rowCell_lane L td H 0 (by omega), rowCell_nonblank L td hb H (by omega), h0⟩

/-- Preloading: every square gets `R Q` home tiles. -/
theorem exists_preload (td : TDims n k s q) (R : Sq k → ℕ)
    (hR : ∀ Q, R Q + 2 ≤ (s - q) * (s - q)) :
    ∀ m (B : Board n), deficit L td R B = m → reservoir k s (sqOf td.hd (blank B)) (blank B) →
      ∃ C : Board n, ∃ p : Path B C, blank C = blank B ∧ (∀ Q, R Q ≤ homeCnt L td C Q) ∧
        p.length ≤ 52 * n * m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro B hm hb
    by_cases hall : ∀ Q, R Q ≤ homeCnt L td B Q
    · exact ⟨B, Path.nil B, rfl, hall, by simp⟩
    push Not at hall
    obtain ⟨Q, hQ⟩ := hall
    have hs2 : R Q + 2 ≤ s ^ 2 := by
      have := hR Q
      have : (s - q) * (s - q) ≤ s ^ 2 := by rw [sq]; exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      omega
    obtain ⟨a, ha, ha0, haQ⟩ := exists_wrong_cell L td B Q (R Q) (hR Q) hQ
    obtain ⟨b, hbr, hb0, hbQ⟩ := exists_home_outside L td B Q (R Q) hs2 hQ
    obtain ⟨c, hc, hc0, hcb⟩ := exists_lane_cell L td B hb b
    have hab : a ≠ b := fun e => hbr (e ▸ ha)
    have hac : a ≠ c := fun e => ha.2.2 (e ▸ hc)
    have hn6 : 6 ≤ n := by
      have := td.hd.band_le (b := 1) (by have := td.hd.two_le; omega)
      have := td.hd.room; have := td.hd.two_le; omega
    obtain ⟨C, p, hp, hbC, hCa, hCb, hCc, hfix⟩ := exists_three_cycle_sharp B hn6 a b c hab hac
      (Ne.symm hcb) (fun e => ha0 (by rw [e]; rfl)) (fun e => hb0 (by rw [e]; rfl))
      (fun e => hc0 (by rw [e]; rfl))
    obtain ⟨hmono, hinc⟩ := homeCnt_step L td B C Q a b c ha haQ hbr hbQ hb0 hc hCa hfix
    have hdef : deficit L td R C + 1 ≤ deficit L td R B := by
      unfold deficit
      rw [← add_sum_erase _ _ (mem_univ Q), ← add_sum_erase _ _ (mem_univ Q)]
      have : ∑ Q' ∈ univ.erase Q, (R Q' - homeCnt L td C Q') ≤
          ∑ Q' ∈ univ.erase Q, (R Q' - homeCnt L td B Q') :=
        sum_le_sum fun Q' _ => by have := hmono Q'; omega
      omega
    have hbC' : reservoir k s (sqOf td.hd (blank C)) (blank C) := by rw [hbC]; exact hb
    obtain ⟨D, p2, hbD, hD, hp2⟩ := ih (deficit L td R C) (by omega) C rfl hbC'
    refine ⟨D, p.append p2, hbD.trans hbC, hD, ?_⟩
    rw [Path.length_append]
    have : 52 * n * deficit L td R C + 52 * n ≤ 52 * n * m := by
      rw [← mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
    omega

end SlidingPuzzle.Tree
