import SlidingPuzzle.Tree.GeomRow

/-! # hopR: along a row lane, into its landing square

Phase 1: the blank walks inside the landing square's reservoir, jumps into the
landing strip and walks along the row through the strip into the lane up to
the insertion position `p`; the lane's positions `1..p` move one step toward
the landing square and the head drops into the strip. Phase 2
(`insert_by_cycle`) jumps into the source's reservoir and places the inserted
tile at `p`. -/
namespace SlidingPuzzle.Tree
open Classical
open SlidingPuzzle.Hub

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

theorem blen_pos_of_in {H : LaneI k q} {J : Fin k} (hJ : LIn L H J) : 0 < blen L H := by
  unfold LIn InPiece at hJ
  split at hJ <;> omega

/-- Phase 1 of a row hop. -/
theorem hopR_phase1 (td : TDims n k s q) (B : Board n) {H : LaneI k q} {J : Fin k}
    (hJ : LIn L H J) (hbl : reservoir k s (rowLand H) (blank B)) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = rowCell s H (rowPos k s H J) ∧
      (∀ x, key L td.hd x = none → (∀ r, r ≤ rowPos k s H J → x ≠ rowCell s H r) →
        C x = B x) ∧
      (∀ r, r < rowPos k s H J → C (rowCell s H r) = B (rowCell s H (r + 1))) ∧
      (∀ x, key L td.hd x ≠ none → key L td.hd x ≠ some (rowLand H) → C x = B x) ∧
      KeepKey L td.hd B C {B (rowCell s H 0)} ∧
      key L td.hd (position C (B (rowCell s H 0))) = some (rowLand H) ∧
      p.inefficientMoves ≤ 3 * s + 7 * (k + 1) +
        ((Finset.range (rowPos k s H J + 1)).filter fun r =>
          ¬ rowGood H (classOf td.hd (B (rowCell s H r)))).card := by
  set h := rowLand H with hh
  set p := rowPos k s H J with hp
  obtain ⟨hpl, -⟩ := rowPos_geom L td H J hJ
  rw [← hp] at hpl
  have hpos := blen_pos_of_in L hJ
  have hks := td.k_lt_s
  have hroom := td.hd.room
  have ho := H.o.isLt
  have hqk := td.q_le
  have hb1 := td.band_le H.b.isLt
  have hb2 := td.band_le H.t.isLt
  have h1 : h.1 = H.b := rfl
  have h2 : h.2 = H.t := rfl
  -- A: walk to the reservoir corner
  let e0 : Cell n := mkCell n (H.b.val * s + k) (H.t.val * s + k)
  have e0f : e0.1.val = H.b.val * s + k := mkCell_fst (by omega)
  have e0s : e0.2.val = H.t.val * s + k := mkCell_snd (by omega)
  have he0 : reservoir k s h e0 := (reservoir_iff td.hd).mpr (by rw [h1, h2]; omega)
  obtain ⟨B1, p1, hbB1, hl1, hf1, -⟩ := exists_reservoir_walk td.hd B hbl he0
  -- B: jump into the landing strip
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + H.o.val + jp) % 2 = 1 :=
    ⟨if (k + H.o.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  obtain ⟨u0, hu0s, hu0c⟩ : ∃ u0, u0 + 1 ≤ s ∧ lineCol s H u0 = H.t.val * s + k + jp :=
    ⟨if H.side then k + jp else s - 1 - k - jp, by split_ifs <;> omega, by
      unfold lineCol; split_ifs <;> omega⟩
  have hlen : ∀ t, u0 + t ≤ s + p → u0 + t < s + rowLen L s H := fun t ht => by omega
  let f : ℕ → Cell n := fun t => lineCell s H (u0 + t)
  have zf : (f 0).1.val = H.b.val * s + H.o.val := lineCell_fst td H _
  have zs : (f 0).2.val = H.t.val * s + k + jp := by
    rw [lineCell_snd L td H _ (by omega)]; exact hu0c
  obtain ⟨p2, hp2⟩ := exists_vjump_step td.hd.two_le_n B1 (f 0)
    (by rw [hbB1, e0s, zs]; simp only [Nat.dist]; omega)
    (by rw [hbB1, e0f, e0s, zf, zs]; omega)
  let B2 := swapCells B1 (blank B1) (f 0)
  have hbB2 : blank B2 = f 0 := blank_swapCells B1 _
  -- keys of the line
  have kstrip : ∀ t, u0 + t < s → key L td.hd (f t) = some h := fun t ht =>
    key_lineCell_strip L td H hpos _ ht
  have frow : ∀ t, s ≤ u0 + t → u0 + t ≤ s + p → f t = rowCell s H (u0 + t - s) := by
    intro t h1 h2
    change lineCell s H (u0 + t) = _
    rw [← lineCell_rowCell L td H _ (by omega)]
    congr 1; omega
  have kline : ∀ t, s ≤ u0 + t → u0 + t ≤ s + p → key L td.hd (f t) = none := by
    intro t h1 h2
    rw [frow t h1 h2]; exact key_rowCell L td H _ (by omega)
  have hB2 : ∀ x, ¬ reservoir k s h x → x ≠ f 0 → B2 x = B x := by
    intro x h1 h2
    change swapCells B1 (blank B1) (f 0) x = B x
    rw [swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ he0)) h2, hf1 x h1]
  have hB2c : ∀ x, key L td.hd x = none → B2 x = B x := by
    intro x hx
    apply hB2
    · exact fun hr => by rw [key_reservoir L td hr] at hx; cases hx
    · exact ne_of_key L (by rw [hx, kstrip 0 (by omega)]; simp)
  -- C: the line walk
  set d := s + p - u0 with hd'
  obtain ⟨B3, p3, hbB3, hC3, hfix3, hi3⟩ := exists_swap_walk d f
    (fun t T => moveCost (f t) (f (t + 1)) T)
    (fun t t' ht ht' e => by
      have := lineCell_inj L td H (hlen t (by omega)) (hlen t' (by omega)) e
      omega)
    (fun t ht B' hB' => by
      obtain ⟨q, hq⟩ := exists_move_step B' (f (t + 1)) (by
        rw [hB']
        have := lineCell_adj (n := n) L td H (u0 + t) (by omega)
        rwa [show u0 + t + 1 = u0 + (t + 1) by ring] at this)
      exact ⟨q, hq.trans (by rw [hB'])⟩)
    B2 hbB2
  have hfd : f d = rowCell s H p := by rw [frow d (by omega) (by omega)]; congr 1; omega
  have offline : ∀ x, key L td.hd x ≠ some h → (∀ r, r ≤ p → x ≠ rowCell s H r) →
      ∀ t, t ≤ d → x ≠ f t := by
    intro x h1 h2 t ht e
    by_cases hts : u0 + t < s
    · exact h1 (by rw [e]; exact kstrip t hts)
    · exact h2 (u0 + t - s) (by omega) (by rw [e, frow t (by omega) (by omega)])
  have hB3 : ∀ x, key L td.hd x ≠ some h → (∀ r, r ≤ p → x ≠ rowCell s H r) →
      B3 x = B2 x := fun x h1 h2 => hfix3 x (offline x h1 h2)
  -- the head step
  set j := s - 1 - u0 with hj
  have hfj1 : f (j + 1) = rowCell s H 0 := by
    rw [frow (j + 1) (by omega) (by omega)]; congr 1; omega
  refine ⟨B3, (p1.append p2).append p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbB3, hfd]
  · intro x hx hq
    rw [hB3 x (by rw [hx]; simp) hq, hB2c x hx]
  · intro r hr
    have e1 : rowCell (n := n) s H r = f (s + r - u0) := by
      rw [frow _ (by omega) (by omega)]; congr 1; omega
    rw [e1, hC3 _ (by omega), frow _ (by omega) (by omega),
      show u0 + (s + r - u0 + 1) - s = r + 1 by omega]
    exact hB2c _ (key_rowCell L td H _ (by omega))
  · intro x h1 h2
    rw [hB3 x h2 (fun r _ e => h1 (by rw [e]; exact key_rowCell L td H _ (by omega)))]
    apply hB2
    · exact fun hr => h2 (key_reservoir L td hr)
    · exact fun e => h2 (by rw [e]; exact kstrip 0 (by omega))
  · have K1 : KeepKey L td.hd B B1 ∅ := keepKey_of_agree L td.hd (reservoir k s h)
      (fun x y hx hy => by rw [key_reservoir L td hx, key_reservoir L td hy]) hf1
    have K2 : KeepKey L td.hd B1 B2 ∅ := keepKey_of_agree L td.hd (fun x => x = e0 ∨ x = f 0)
      (fun x y hx hy => by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp only [key_reservoir L td he0, kstrip 0 (by omega)])
      (fun x hx => by
        simp only [not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    have K3 := keepKey_of_walk L td.hd f d j hbB2
      (fun t ht htj => by
        by_cases h1 : u0 + t + 1 < s
        · rw [kstrip t (by omega), kstrip (t + 1) (by omega)]
        · rw [kline t (by omega) (by omega), kline (t + 1) (by omega) (by omega)])
      hC3 hfix3
    rw [hfj1, hB2c _ (key_rowCell L td H _ (by omega))] at K3
    simpa using (K1.trans K2).trans K3
  · have e := hC3 j (by omega)
    rw [hfj1, hB2c _ (key_rowCell L td H _ (by omega))] at e
    rw [position_eq_of_apply e]
    exact kstrip j (by omega)
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
    have s2 : ∑ r ∈ Finset.range (p + 1), moveCost (f (j + r)) (f (j + r + 1)) (B2 (f (j + r + 1)))
        ≤ ((Finset.range (p + 1)).filter fun r =>
          ¬ rowGood H (classOf td.hd (B (rowCell s H r)))).card := by
      rw [Finset.card_filter]
      apply Finset.sum_le_sum
      intro r hr
      rw [Finset.mem_range] at hr
      have ej : f (j + r) = lineCell s H (s - 1 + r) := by
        show lineCell s H _ = _; congr 1; omega
      have ef : f (j + r + 1) = lineCell s H (s - 1 + r + 1) := by
        show lineCell s H _ = _; congr 1; omega
      have et : lineCell (n := n) s H (s - 1 + r + 1) = rowCell s H r := by
        rw [← lineCell_rowCell L td H r (by omega)]; congr 1; omega
      have htile : B2 (lineCell s H (s - 1 + r + 1)) = B (rowCell s H r) := by
        rw [et]; exact hB2c _ (key_rowCell L td H _ (by omega))
      rw [ej, ef, htile]
      by_cases hg : rowGood H (classOf td.hd (B (rowCell s H r)))
      · rw [moveCost_lineCell (n := n) L td H (s - 1 + r) (by omega) (by omega) _ hg]
        exact Nat.zero_le _
      · rw [if_pos hg]; exact moveCost_le_one _ _ _
    omega

/-- The corner of the source's box used by the insertion: top right for lanes
after the landing block, top left for lanes before it. -/
theorem hopR_cornerDist (td : TDims n k s q) {S : Sq k} {H : LaneI k q} {v w : Cell n}
    (right : Bool) (vf : v.1.val = S.1.val * s + H.o.val)
    (vs : v.2.val = if right then S.2.val * s + s - 1 else S.2.val * s + k)
    (wf : w.1.val = S.1.val * s + k) (hw3 : Nat.dist v.2.val w.2.val ≤ 1)
    (hw1 : S.2.val * s + k ≤ w.2.val) (hw2 : w.2.val < S.2.val * s + s) :
    ∀ j, j ≤ 2 → cornerDist (S.1.val * s) (S.2.val * s) s false right w v
      (mkCell n (S.1.val * s + (k + 2)) (S.2.val * s + (if right then s - 3 else k) + j)) ≤
        6 * k + 7 := by
  intro j hj
  have hroom := td.hd.room
  have hb1 := td.band_le S.1.isLt
  have hb2 := td.band_le S.2.isLt
  have ho := H.o.isLt
  have hqk := td.q_le
  cases right
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true] at vs ⊢
    unfold cornerDist reflC
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [mkCell_fst (by omega), mkCell_snd (by omega), wf, vf]
    rw [vs] at hw3
    simp only [Nat.dist] at hw3 ⊢
    omega

/-- A row hop realized on the board. -/
theorem simulate_hopR (td : TDims n k s q) {B : Board n} {σ : IState k q} (hR : Rel L td.hd B σ)
    {H : LaneI k q} {J : Fin k} {y : Sq k} (hpre : σ.Pre L (.hopR H J y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel L td.hd C (σ.step s (.hopR H J y)) ∧
      p.inefficientMoves ≤ σ.cost s (.hopR H J y) := by
  obtain ⟨hbl, hJ, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl⟩ := hR
  rw [hbl] at hRbl
  set S : Sq k := (H.b, J) with hSdef
  set h := rowLand H with hh
  set p := rowPos k s H J with hp
  obtain ⟨hpl, hvcol⟩ := rowPos_geom L td H J hJ
  rw [← hp] at hpl hvcol
  obtain ⟨B3, p3, hb3, hA, hBrow, hBreg, K1, hkhead, hi3⟩ := hopR_phase1 L td B hJ hRbl
  rw [← hp] at hi3
  have hSh : S ≠ h := by
    intro e
    have := congrArg Prod.snd e
    simp only [hSdef, hh, rowLand] at this
    have hne := LaneSys.inPiece_lt hJ
    rcases hne with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [this] at h' <;> omega
  have hks := td.k_lt_s
  have hroom := td.hd.room
  have hqk := td.q_le
  have ho := H.o.isLt
  have hbS1 := td.band_le H.b.isLt
  have hbS2 := td.band_le J.isLt
  -- the insertion cell and the jump target
  set v := rowCell (n := n) s H p with hv
  have vf : v.1.val = H.b.val * s + H.o.val := rowCell_fst td H p
  have vs : v.2.val = rowCol s H p := rowCell_snd L td H p hpl
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + H.o.val + jp) % 2 = 1 :=
    ⟨if (k + H.o.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  obtain ⟨wc, hwc1, hwc2, hwc3, hwc4⟩ : ∃ wc, J.val * s + k ≤ wc ∧ wc < J.val * s + s ∧
      Nat.dist (rowCol s H p) wc ≤ 1 ∧ (rowCol s H p + wc + jp) % 2 = 0 := by
    refine ⟨if H.side then J.val * s + s - 1 - jp else J.val * s + k + jp, ?_⟩
    rw [hvcol]; simp only [Nat.dist]; split_ifs <;> omega
  let w : Cell n := mkCell n (H.b.val * s + k) wc
  have wf : w.1.val = H.b.val * s + k := mkCell_fst (by omega)
  have ws : w.2.val = wc := mkCell_snd (by omega)
  have hw : reservoir k s S w := (reservoir_iff td.hd).mpr (by simp only [hSdef]; omega)
  have hkv : key L td.hd v = none := key_rowCell L td H p hpl
  have hvbox : InBox (S.1.val * s) (S.2.val * s) s v := by
    unfold InBox; simp only [hSdef]; rw [vf, vs, hvcol]; split_ifs <;> omega
  have hreg3 : ∀ x, region L s S x → B3 x = B x := fun x hx =>
    hBreg x (by rw [(key_eq_some L td.hd).mpr hx]; simp)
      (by rw [(key_eq_some L td.hd).mpr hx]; exact fun e => hSh (Option.some.inj e))
  obtain ⟨t, htQ, htT, htc⟩ := exists_of_regionCount L td.hd B3 (Q := S) (y := y) (by
      rw [regionCount_congr L td.hd hreg3, hRcnt]; exact hcnt)
  obtain ⟨p4, hp4⟩ := exists_vjump_step td.hd.two_le_n B3 w
    (by rw [hb3, vs, ws]; exact hwc3) (by rw [hb3]; omega)
  have hwc3' : Nat.dist v.2.val w.2.val ≤ 1 := by rw [vs, ws]; exact hwc3
  have hD := hopR_cornerDist td (S := S) (H := H) H.side vf (vs.trans hvcol) wf hwc3'
    (by rw [ws]; exact hwc1) (by rw [ws]; exact hwc2)
  obtain ⟨C, p5, T, hT0, hTc, hTk, hCv, hCbl, hCx, hCfp, K2, hi5⟩ :=
    insert_by_cycle L td B3 (Q := S) (y := y) hb3 hkv hw hvbox t htQ htT htc
      (7 * (k + 1)) ⟨p4, hp4.trans (by rw [hb3]; simp only [Nat.dist]; omega)⟩
      false H.side (ro := k + 2) (co := if H.side then s - 3 else k) (by omega) (by omega)
      (by split_ifs <;> omega) (by split_ifs <;> omega) hD
  have hCc : ∀ x, key L td.hd x = none → x ≠ v → C x = B3 x := fun x hx hxv =>
    hCx x hxv (by rw [hx]; simp)
  set head := B (rowCell s H 0) with hhead
  have hhead0 : head.val ≠ 0 := (hRrow H 0 (by omega)).1
  have hkB3T : key L td.hd (position B3 T) = some S := hTk
  have hTh : head ≠ T := by
    intro e
    rw [← e, hkhead] at hkB3T
    exact hSh (Option.some.inj hkB3T).symm
  refine ⟨C, p3.append p5, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- row lanes
    intro H' q' hq'
    simp only [IState.step]
    by_cases e : H' = H ∧ q' ≤ p
    · obtain ⟨rfl, hq'p⟩ := e
      rw [Function.update_self]
      unfold shiftIn
      rcases Nat.lt_or_ge q' p with hlt | hge
      · rw [if_pos hlt, hCc _ (key_rowCell L td H' q' hq')
          (fun e => by have := (rowCell_inj L td hq' hpl e).2; omega), hBrow q' hlt]
        exact hRrow H' (q' + 1) (by omega)
      · have hq : q' = p := by omega
        subst hq
        rw [if_neg (lt_irrefl _), if_pos rfl, hCv, hTc]
        exact ⟨hT0, rfl⟩
    · have hne : ∀ r, r ≤ p → rowCell (n := n) s H' q' ≠ rowCell s H r := by
        intro r hr e'
        obtain ⟨h1, h2⟩ := rowCell_inj L td hq' (by omega) e'
        exact e ⟨h1, by omega⟩
      rw [hCc _ (key_rowCell L td H' q' hq') (hne p le_rfl),
        hA _ (key_rowCell L td H' q' hq') hne]
      by_cases eH : H' = H
      · subst eH
        rw [Function.update_self]
        unfold shiftIn
        have : ¬ q' ≤ p := fun hh => e ⟨rfl, hh⟩
        rw [if_neg (by omega), if_neg (by omega)]
        exact hRrow H' q' hq'
      · rw [Function.update_of_ne eH]
        exact hRrow H' q' hq'
  · -- column lanes
    intro V r hr
    simp only [IState.step]
    have hk := key_colCell L td V r hr
    rw [hCc _ hk (fun e => rowCell_ne_colCell L td H V p r hr e.symm),
      hA _ hk (fun r' _ e => rowCell_ne_colCell L td H V r' r hr e.symm)]
    exact hRcol V r hr
  · -- region counts
    intro Q y'
    simp only [IState.step]
    have K : KeepKey L td.hd B C {head, T} := by
      have := K1.trans K2
      rwa [← Finset.insert_eq] at this
    have k1C : key L td.hd (position C head) = some h := by
      rw [K2 head hhead0 (by simpa using hTh), hkhead]
    have k2B : key L td.hd (position B T) = some S := by
      rw [← K1 T hT0 (by simpa using hTh.symm)]; exact hkB3T
    have k1B : key L td.hd (position B head) = none := by
      rw [show position B head = rowCell s H 0 by simp [hhead, position]]
      exact key_rowCell L td H 0 (by omega)
    have k2C : key L td.hd (position C T) = none := by
      rw [position_eq_of_apply hCv]; exact hkv
    rw [regionCount_move2 L td.hd K hTh hhead0 hT0 hSh k1B k1C k2B k2C Q y', hTc,
      (hRrow H 0 (by omega)).2]
    have hc : regionCount L td.hd B = σ.cnt := funext fun Q => funext fun y => hRcnt Q y
    rw [hc]
  · -- the blank
    simp only [IState.step]
    rw [hCbl]; exact hw
  · -- cost
    simp only [IState.cost, IState.junkRow]
    rw [Path.inefficientMoves_append]
    have hj : ((Finset.range (p + 1)).filter fun r =>
        ¬ rowGood H (classOf td.hd (B (rowCell s H r)))) =
        ((Finset.range (p + 1)).filter fun r => ¬ rowGood H (σ.row H r)) := by
      apply Finset.filter_congr
      intro r hr
      rw [Finset.mem_range] at hr
      rw [(hRrow H r (by omega)).2]
    rw [hj] at hi3
    change _ ≤ 20 * s + 600 * k + 2000 +
      ((Finset.range (p + 1)).filter fun r => ¬ rowGood H (σ.row H r)).card
    omega

end SlidingPuzzle.Tree
