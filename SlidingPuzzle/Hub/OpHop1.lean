import SlidingPuzzle.Hub.GeomHop1
import SlidingPuzzle.Hub.OpInsert

/-! # hop1: along the row, into the hub

Phase 1: the blank walks inside the hub's reservoir, jumps into the landing
strip and walks along the row `R(h)` through the strip into the half up to the
insertion position `p`; the half's positions `1..p` move one step toward the
hub and the head drops into the strip. Phase 2 (`insert_by_cycle`) jumps into
the source's reservoir and places the inserted tile at `p`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- Phase 1 of hop1. -/
theorem hop1_phase1 (hd : HDims n k s) (B : Board n) {S h : Sq k}
    (hbl : reservoir k s h (blank B)) (hne : S.2 ≠ h.2) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = rowCell k s (hop1Half S h) (hop1Pos s S h) ∧
      (∀ x, keyOf hd x = none → (∀ q, q ≤ hop1Pos s S h → x ≠ rowCell k s (hop1Half S h) q) →
        C x = B x) ∧
      (∀ q, q < hop1Pos s S h →
        C (rowCell k s (hop1Half S h) q) = B (rowCell k s (hop1Half S h) (q + 1))) ∧
      (∀ x, keyOf hd x ≠ none → keyOf hd x ≠ some h → C x = B x) ∧
      KeepKey hd B C {B (rowCell k s (hop1Half S h) 0)} ∧
      keyOf hd (position C (B (rowCell k s (hop1Half S h) 0))) = some h ∧
      (∀ b, dcell k s h b ≠ blank B → C (dcell k s h b) = B (dcell k s h b)) ∧
      p.inefficientMoves ≤ 3 * s + 7 * (k + 1) +
        ((Finset.range (hop1Pos s S h + 1)).filter fun q =>
          (classOf hd (B (rowCell k s (hop1Half S h) q))).2 ≠ h.2).card := by
  set H := hop1Half S h with hH
  set p := hop1Pos s S h with hp
  obtain ⟨hpl, -⟩ := hop1_geom hd hne
  rw [← hH, ← hp] at hpl
  have hH1 : H.1 = h.1 := rfl
  have hH2 : H.2.1 = h.2 := rfl
  have hHh : ((H.1, H.2.1) : Sq k) = h := rfl
  have hks := hd.k_lt_s
  have hroom := hd.room
  have hc := h.2.isLt
  have hb1 := hd.band_le h.1.isLt
  have hb2 := hd.band_le h.2.isLt
  -- A: walk to the reservoir corner
  let e0 : Cell n := mkCell n (h.1.val * s + k) (h.2.val * s + k)
  have e0f : e0.1.val = h.1.val * s + k := mkCell_fst (by omega)
  have e0s : e0.2.val = h.2.val * s + k := mkCell_snd (by omega)
  have he0 : reservoir k s h e0 := (reservoir_iff hd).mpr (by omega)
  obtain ⟨B1, p1, hbB1, hl1, hf1, hdc1⟩ := exists_reservoir_walk hd B hbl he0
  -- B: jump into the landing strip
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + h.2.val + jp) % 2 = 1 :=
    ⟨if (k + h.2.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  obtain ⟨u0, hu0s, hu0c⟩ : ∃ u0, u0 + 1 ≤ s ∧ lineCol s H u0 = h.2.val * s + k + jp :=
    ⟨if H.2.2 then k + jp else s - 1 - k - jp, by split_ifs <;> omega, by
      unfold lineCol; rw [hH2]; split_ifs <;> omega⟩
  have hlen : ∀ t, u0 + t ≤ s + p → u0 + t < s + rowLen k s H := fun t ht => by omega
  let f : ℕ → Cell n := fun t => lineCell k s H (u0 + t)
  have zf : (f 0).1.val = h.1.val * s + h.2.val := lineCell_fst hd H _
  have zs : (f 0).2.val = h.2.val * s + k + jp := by
    rw [lineCell_snd hd H _ (by omega)]; exact hu0c
  obtain ⟨p2, hp2⟩ := exists_vjump_step hd.two_le_n B1 (f 0)
    (by rw [hbB1, e0s, zs]; simp only [Nat.dist]; omega)
    (by rw [hbB1, e0f, e0s, zf, zs]; omega)
  let B2 := swapCells B1 (blank B1) (f 0)
  have hbB2 : blank B2 = f 0 := blank_swapCells B1 _
  -- keys of the line
  have kstrip : ∀ t, u0 + t < s → keyOf hd (f t) = some h := fun t ht => by
    rw [← hHh]; exact keyOf_lineCell_strip hd H _ ht
  have frow : ∀ t, s ≤ u0 + t → u0 + t ≤ s + p → f t = rowCell k s H (u0 + t - s) := by
    intro t h1 h2
    change lineCell k s H (u0 + t) = _
    rw [← lineCell_rowCell hd H _ (by omega)]
    congr 1; omega
  have kline : ∀ t, s ≤ u0 + t → u0 + t ≤ s + p → keyOf hd (f t) = none := by
    intro t h1 h2
    rw [frow t h1 h2]; exact keyOf_rowCell hd H _ (by omega)
  -- B2 agrees with B away from the hub's reservoir and the strip cell
  have hB2 : ∀ x, ¬ reservoir k s h x → x ≠ f 0 → B2 x = B x := by
    intro x h1 h2
    change swapCells B1 (blank B1) (f 0) x = B x
    rw [swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ he0)) h2, hf1 x h1]
  have hB2c : ∀ x, keyOf hd x = none → B2 x = B x := by
    intro x hx
    apply hB2
    · exact fun hr => by rw [keyOf_reservoir hd hr] at hx; cases hx
    · exact ne_of_keyOf (by rw [hx, kstrip 0 (by omega)]; simp)
  -- C: the line walk
  set d := s + p - u0 with hd'
  obtain ⟨B3, p3, hbB3, hC3, hfix3, hi3⟩ := exists_swap_walk d f
    (fun t T => moveCost (f t) (f (t + 1)) T)
    (fun t t' ht ht' e => by
      have := lineCell_inj hd H (hlen t (by omega)) (hlen t' (by omega)) e
      omega)
    (fun t ht B' hB' => by
      obtain ⟨q, hq⟩ := exists_move_step B' (f (t + 1)) (by
        rw [hB']
        have := lineCell_adj (n := n) hd H (u0 + t) (by omega)
        rwa [show u0 + t + 1 = u0 + (t + 1) by ring] at this)
      exact ⟨q, hq.trans (by rw [hB'])⟩)
    B2 hbB2
  have hfd : f d = rowCell k s H p := by rw [frow d (by omega) (by omega)]; congr 1; omega
  -- off the line
  have offline : ∀ x, keyOf hd x ≠ some h → (∀ q, q ≤ p → x ≠ rowCell k s H q) →
      ∀ t, t ≤ d → x ≠ f t := by
    intro x h1 h2 t ht e
    by_cases hts : u0 + t < s
    · exact h1 (by rw [e]; exact kstrip t hts)
    · exact h2 (u0 + t - s) (by omega) (by rw [e, frow t (by omega) (by omega)])
  have hB3 : ∀ x, keyOf hd x ≠ some h → (∀ q, q ≤ p → x ≠ rowCell k s H q) →
      B3 x = B2 x := fun x h1 h2 => hfix3 x (offline x h1 h2)
  -- the head step
  set j := s - 1 - u0 with hj
  have hfj1 : f (j + 1) = rowCell k s H 0 := by
    rw [frow (j + 1) (by omega) (by omega)]; congr 1; omega
  refine ⟨B3, (p1.append p2).append p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbB3, hfd]
  · intro x hx hq
    rw [hB3 x (by rw [hx]; simp) hq, hB2c x hx]
  · intro q hq
    have e1 : rowCell k s H q = f (s + q - u0) := by
      rw [frow _ (by omega) (by omega)]; congr 1; omega
    rw [e1, hC3 _ (by omega), frow _ (by omega) (by omega),
      show u0 + (s + q - u0 + 1) - s = q + 1 by omega]
    exact hB2c _ (keyOf_rowCell hd H _ (by omega))
  · intro x h1 h2
    rw [hB3 x h2 (fun q _ e => h1 (by rw [e]; exact keyOf_rowCell hd H _ (by omega)))]
    apply hB2
    · exact fun hr => h2 (keyOf_reservoir hd hr)
    · exact fun e => h2 (by rw [e]; exact kstrip 0 (by omega))
  · have K1 : KeepKey hd B B1 ∅ := keepKey_of_agree hd (reservoir k s h)
      (fun x y hx hy => by rw [keyOf_reservoir hd hx, keyOf_reservoir hd hy]) hf1
    have K2 : KeepKey hd B1 B2 ∅ := keepKey_of_agree hd (fun x => x = e0 ∨ x = f 0)
      (fun x y hx hy => by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp only [keyOf_reservoir hd he0, kstrip 0 (by omega)])
      (fun x hx => by
        simp only [not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    have K3 := keepKey_of_walk hd f d j hbB2
      (fun t ht htj => by
        by_cases h1 : u0 + t + 1 < s
        · rw [kstrip t (by omega), kstrip (t + 1) (by omega)]
        · rw [kline t (by omega) (by omega), kline (t + 1) (by omega) (by omega)])
      hC3 hfix3
    rw [hfj1, hB2c _ (keyOf_rowCell hd H _ (by omega))] at K3
    simpa using (K1.trans K2).trans K3
  · have e := hC3 j (by omega)
    rw [hfj1, hB2c _ (keyOf_rowCell hd H _ (by omega))] at e
    rw [position_eq_of_apply e]
    exact kstrip j (by omega)
  · -- the designated cells of the hub
    intro b hb
    have df := dcell_fst (n := n) hd h b
    have hne0 : dcell (n := n) k s h b ≠ e0 := fun e => by
      rw [e, e0f] at df; omega
    have hne1 : dcell (n := n) k s h b ≠ f 0 := fun e => by
      rw [e, zf] at df; omega
    have hoff : ∀ t, t ≤ d → dcell (n := n) k s h b ≠ f t := fun t _ e => by
      have := lineCell_fst (n := n) hd H (u0 + t)
      change (f t).1.val = _ at this
      rw [← e, df, hH1, hH2] at this; omega
    rw [hfix3 _ hoff]
    change swapCells B1 (blank B1) (f 0) (dcell k s h b) = _
    rw [swapCells_preserves B1 (by rw [hbB1]; exact hne0) hne1]
    exact hdc1 b hb hne0
  · -- cost
    rw [Path.inefficientMoves_append, Path.inefficientMoves_append]
    have c1 := p1.inefficientMoves_le_length
    have c2 : 7 * (Nat.dist (blank B1).1.val (f 0).1.val + 1) ≤ 7 * (k + 1) := by
      rw [hbB1, e0f, zf]; simp only [Nat.dist]; omega
    have hdsplit : d = j + (p + 1) := by omega
    rw [hdsplit, Finset.sum_range_add] at hi3
    have s1 : ∑ t ∈ Finset.range j, moveCost (f t) (f (t + 1)) (B2 (f (t + 1))) ≤ s := by
      calc _ ≤ ∑ t ∈ Finset.range j, 1 := Finset.sum_le_sum fun t _ => moveCost_le_one _ _ _
        _ ≤ s := by simp; omega
    have s2 : ∑ q ∈ Finset.range (p + 1), moveCost (f (j + q)) (f (j + q + 1)) (B2 (f (j + q + 1)))
        ≤ ((Finset.range (p + 1)).filter fun q =>
          (classOf hd (B (rowCell k s H q))).2 ≠ h.2).card := by
      rw [Finset.card_filter]
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.mem_range] at hq
      have ej : f (j + q) = lineCell k s H (s - 1 + q) := by
        show lineCell k s H _ = _; congr 1; omega
      have ef : f (j + q + 1) = lineCell k s H (s - 1 + q + 1) := by
        show lineCell k s H _ = _; congr 1; omega
      have et : lineCell (n := n) k s H (s - 1 + q + 1) = rowCell k s H q := by
        rw [← lineCell_rowCell hd H q (by omega)]; congr 1; omega
      have htile : B2 (lineCell k s H (s - 1 + q + 1)) = B (rowCell k s H q) := by
        rw [et]; exact hB2c _ (keyOf_rowCell hd H _ (by omega))
      rw [ej, ef, htile]
      split_ifs with hjunk
      · exact moveCost_le_one _ _ _
      · push Not at hjunk
        rw [moveCost_lineCell (n := n) hd H (s - 1 + q) (by omega) (by omega) _ hjunk]
    omega

/-- The corner of `S`'s box used by the insertion of a hop1: top right for right
halves, top left for left halves. -/
theorem hop1_cornerDist (hd : HDims n k s) {S h : Sq k} {v w : Cell n} (right : Bool)
    (hS1 : S.1.val * s = h.1.val * s) (vf : v.1.val = h.1.val * s + h.2.val)
    (vs : v.2.val = if right then S.2.val * s + s - 1 else S.2.val * s + k)
    (wf : w.1.val = S.1.val * s + k) (hw3 : Nat.dist v.2.val w.2.val ≤ 1)
    (hw1 : S.2.val * s + k ≤ w.2.val) (hw2 : w.2.val < S.2.val * s + s) :
    ∀ j, j ≤ 2 → cornerDist (S.1.val * s) (S.2.val * s) s false right w v
      (mkCell n (S.1.val * s + (k + 2)) (S.2.val * s + (if right then s - 3 else k) + j)) ≤
        6 * k + 7 := by
  intro j hj
  have hroom := hd.room
  have hb1 := hd.band_le S.1.isLt
  have hb2 := hd.band_le S.2.isLt
  have hh2 := h.2.isLt
  cases right
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true] at vs ⊢
    unfold cornerDist reflC
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [mkCell_fst (by omega), mkCell_snd (by omega), wf, vf, hS1]
    rw [vs] at hw3
    simp only [Nat.dist] at hw3 ⊢
    omega

/-- hop1 realized on the board. -/
theorem simulate_hop1 (hd : HDims n k s) {B : Board n} {σ : IState k} (hR : Rel hd B σ)
    {S h y : Sq k} (hpre : σ.Pre (.hop1 S h y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.hop1 S h y)) ∧
      p.inefficientMoves ≤ σ.cost s (.hop1 S h y) := by
  obtain ⟨hbl, hS1, hS2, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl, hRd⟩ := hR
  rw [hbl] at hRbl
  set H := hop1Half S h with hH
  set p := hop1Pos s S h with hp
  obtain ⟨hpl, hvcol⟩ := hop1_geom hd hS2
  rw [← hH, ← hp] at hpl hvcol
  obtain ⟨B3, p3, hb3, hA, hBrow, hBreg, K1, hkhead, hdc3, hi3⟩ := hop1_phase1 hd B hRbl hS2
  rw [← hp] at hi3
  have hH1 : H.1 = h.1 := rfl
  have hH2 : H.2.1 = h.2 := rfl
  have hSh : S ≠ h := fun e => hS2 (by rw [e])
  have hks := hd.k_lt_s
  have hroom := hd.room
  have hc := h.2.isLt
  have hJ := S.2.isLt
  have hbS1 := hd.band_le S.1.isLt
  have hbS2 := hd.band_le S.2.isLt
  have hS1' : S.1.val * s = h.1.val * s := by rw [hS1]
  -- the insertion cell and the jump target
  set v := rowCell (n := n) k s H p with hv
  have vf : v.1.val = h.1.val * s + h.2.val := rowCell_fst hd H p
  have vs : v.2.val = rowCol s H p := rowCell_snd hd H p hpl
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + h.2.val + jp) % 2 = 1 :=
    ⟨if (k + h.2.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  obtain ⟨wc, hwc1, hwc2, hwc3, hwc4⟩ : ∃ wc, S.2.val * s + k ≤ wc ∧ wc < S.2.val * s + s ∧
      Nat.dist (rowCol s H p) wc ≤ 1 ∧ (rowCol s H p + wc + jp) % 2 = 0 := by
    refine ⟨if H.2.2 then S.2.val * s + s - 1 - jp else S.2.val * s + k + jp, ?_⟩
    rw [hvcol]; simp only [Nat.dist]; split_ifs <;> omega
  let w : Cell n := mkCell n (S.1.val * s + k) wc
  have wf : w.1.val = S.1.val * s + k := mkCell_fst (by omega)
  have ws : w.2.val = wc := mkCell_snd (by omega)
  have hw : reservoir k s S w := (reservoir_iff hd).mpr (by omega)
  have hkv : keyOf hd v = none := keyOf_rowCell hd H p hpl
  have hvbox : InBox (S.1.val * s) (S.2.val * s) s v := by
    unfold InBox; rw [vf, vs, hvcol]; split_ifs <;> omega
  have hreg3 : ∀ x, region k s S x → B3 x = B x := fun x hx =>
    hBreg x (by rw [(keyOf_eq_some hd).mpr hx]; simp)
      (by rw [(keyOf_eq_some hd).mpr hx]; exact fun e => hSh (Option.some.inj e))
  obtain ⟨t, htF, htQ, htT, htc⟩ := exists_of_regionCount_avoid hd B3
    (validD (n := n) (s := s) σ S y) (by
      have := card_validD_le (n := n) (s := s) σ S y
      rw [regionCount_congr hd hreg3, hRcnt]
      exact (Nat.add_le_add_right this 1).trans hcnt)
  have htd : ∀ b y', σ.des S b = some y' → t ≠ dcell k s S b := by
    intro b y' hb e
    have h1 := (hRd S b y' hb).2
    rw [← e, ← hreg3 t htQ, htc] at h1
    subst h1
    exact htF (e ▸ mem_validD hb)
  obtain ⟨p4, hp4⟩ := exists_vjump_step hd.two_le_n B3 w
    (by rw [hb3, vs, ws]; exact hwc3) (by rw [hb3]; omega)
  -- the three-cycle is staged from the top corner of `S`'s box on the side of `v`
  have hwc3' : Nat.dist v.2.val w.2.val ≤ 1 := by rw [vs, ws]; exact hwc3
  have hD := hop1_cornerDist hd (h := h) H.2.2 hS1' vf (vs.trans hvcol) wf hwc3'
    (by rw [ws]; exact hwc1) (by rw [ws]; exact hwc2)
  obtain ⟨C, p5, T, hT0, hTc, hTk, hCv, hCbl, hCx, hCfp, K2, hi5⟩ :=
    insert_by_cycle hd B3 (Q := S) (y := y) hb3 hkv hw hvbox t htQ htT htc
      (7 * (k + 1)) ⟨p4, hp4.trans (by rw [hb3]; simp only [Nat.dist]; omega)⟩
      false H.2.2 (ro := k + 2) (co := if H.2.2 then s - 3 else k) (by omega) (by omega)
      (by split_ifs <;> omega) (by split_ifs <;> omega) hD
  -- facts about C
  have hCc : ∀ x, keyOf hd x = none → x ≠ v → C x = B3 x := fun x hx hxv =>
    hCx x hxv (by rw [hx]; simp)
  set head := B (rowCell k s H 0) with hhead
  have hhead0 : head.val ≠ 0 := (hRrow H 0 (by omega)).1
  have hkB3T : keyOf hd (position B3 T) = some S := hTk
  have hTh : head ≠ T := by
    intro e
    rw [← e, hkhead] at hkB3T
    exact hSh (Option.some.inj hkB3T).symm
  refine ⟨C, p3.append p5, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- row halves
    intro H' q' hq'
    simp only [IState.step]
    by_cases e : H' = H ∧ q' ≤ p
    · obtain ⟨rfl, hq'p⟩ := e
      rw [Function.update_self]
      unfold shiftIn
      rcases Nat.lt_or_ge q' p with hlt | hge
      · rw [if_pos hlt, hCc _ (keyOf_rowCell hd H q' hq')
          (fun e => by have := (rowCell_inj hd hq' hpl e).2; omega), hBrow q' hlt]
        exact hRrow H (q' + 1) (by omega)
      · have hq : q' = p := by omega
        subst hq
        rw [if_neg (lt_irrefl _), if_pos rfl, hCv, hTc]
        exact ⟨hT0, rfl⟩
    · have hne : ∀ q, q ≤ p → rowCell (n := n) k s H' q' ≠ rowCell k s H q := by
        intro q hq e'
        obtain ⟨h1, h2⟩ := rowCell_inj hd hq' (by omega) e'
        exact e ⟨h1, by omega⟩
      rw [hCc _ (keyOf_rowCell hd H' q' hq') (hne p le_rfl),
        hA _ (keyOf_rowCell hd H' q' hq') hne]
      by_cases eH : H' = H
      · subst eH
        rw [Function.update_self]
        unfold shiftIn
        have : ¬ q' ≤ p := fun hh => e ⟨rfl, hh⟩
        rw [if_neg (by omega), if_neg (by omega)]
        exact hRrow H q' hq'
      · rw [Function.update_of_ne eH]
        exact hRrow H' q' hq'
  · -- column halves
    intro V q hq
    simp only [IState.step]
    have hk := keyOf_colCell (n := n) hd V q hq
    rw [hCc _ hk (fun e => rowCell_ne_colCell hd H V p q hq e.symm),
      hA _ hk (fun q' _ e => rowCell_ne_colCell hd H V q' q hq e.symm)]
    exact hRcol V q hq
  · -- region counts
    intro Q y'
    simp only [IState.step]
    have K : KeepKey hd B C {head, T} := by
      have := K1.trans K2
      rwa [← Finset.insert_eq] at this
    have k1C : keyOf hd (position C head) = some h := by
      rw [K2 head hhead0 (by simpa using hTh), hkhead]
    have k2B : keyOf hd (position B T) = some S := by
      rw [← K1 T hT0 (by simpa using hTh.symm)]; exact hkB3T
    have k1B : keyOf hd (position B head) = none := by
      rw [show position B head = rowCell k s H 0 by simp [hhead, position]]
      exact keyOf_rowCell hd H 0 (by omega)
    have k2C : keyOf hd (position C T) = none := by
      rw [position_eq_of_apply hCv]; exact hkv
    rw [regionCount_move2 hd K hTh hhead0 hT0 hSh k1B k1C k2B k2C Q y', hTc,
      (hRrow H 0 (by omega)).2]
    have hc : regionCount hd B = σ.cnt := funext fun Q => funext fun y => hRcnt Q y
    rw [hc]
  · -- the blank
    simp only [IState.step]
    rw [hCbl]; exact hw
  · -- designated cells
    intro Q b y' hdes
    simp only [IState.step] at hdes
    have hB := hRd Q b y' hdes
    suffices C (dcell k s Q b) = B (dcell k s Q b) by rw [this]; exact hB
    have hkey : keyOf hd (dcell (n := n) k s Q b) = some Q :=
      keyOf_reservoir hd (reservoir_dcell hd Q b)
    have hv' : dcell (n := n) k s Q b ≠ v := ne_of_keyOf (by rw [hkey, hkv]; simp)
    have hbl' : dcell (n := n) k s Q b ≠ blank B := fun e => hB.1 (by
      rw [e]; simp [blank, position])
    have df := dcell_fst (n := n) hd Q b
    by_cases hQS : Q = S
    · subst hQS
      rw [hCfp _ hv' (fun e => by rw [e, wf] at df; omega) (htd b y' hdes).symm
        (by rw [df]; omega), hreg3 _ (region_of_reservoir (reservoir_dcell hd Q b))]
    · rw [hCx _ hv' (by rw [hkey]; exact fun e => hQS (Option.some.inj e))]
      by_cases hQh : Q = h
      · subst hQh; exact hdc3 b hbl'
      · exact hBreg _ (by rw [hkey]; simp) (by rw [hkey]; exact fun e => hQh (Option.some.inj e))
  · -- cost
    simp only [IState.cost, IState.junkRow]
    rw [Path.inefficientMoves_append]
    have hj : ((Finset.range (p + 1)).filter fun q =>
        (classOf hd (B (rowCell k s H q))).2 ≠ h.2) =
        ((Finset.range (p + 1)).filter fun q => (σ.row H q).2 ≠ H.2.1) := by
      apply Finset.filter_congr
      intro q hq
      rw [Finset.mem_range] at hq
      rw [(hRrow H q (by omega)).2]
      exact Iff.rfl
    rw [hj] at hi3
    change _ ≤ 13 * s + 506 * k + 1024 + ((Finset.range (p + 1)).filter fun q => (σ.row H q).2 ≠ H.2.1).card
    omega

end SlidingPuzzle.Hub