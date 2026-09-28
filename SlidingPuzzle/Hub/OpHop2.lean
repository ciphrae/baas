import SlidingPuzzle.Hub.GeomCol
import SlidingPuzzle.Hub.OpInsert

/-! # hop2: along the column, into the served square

Phase 1: the blank walks inside `D`'s reservoir, jumps horizontally onto `D`'s
own column piece, jumps across the row group into position `0` of the column
half (the head drops into `D`'s region) and walks along the half to the
insertion position `p` (adjacent steps inside a band, jumps of `k+1` between
bands). Phase 2 (`insert_by_cycle`) jumps into the hub's reservoir and places
the inserted tile at `p`. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- Phase 1 of hop2. -/
theorem hop2_phase1 (hd : HDims n k s) (B : Board n) {h D : Sq k}
    (hbl : reservoir k s D (blank B)) (hne : h.1 ≠ D.1) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = colCell k s (hop2Half h D) (hop2Pos s h D) ∧
      (∀ x, keyOf hd x = none → (∀ q, q ≤ hop2Pos s h D → x ≠ colCell k s (hop2Half h D) q) →
        C x = B x) ∧
      (∀ q, q < hop2Pos s h D →
        C (colCell k s (hop2Half h D) q) = B (colCell k s (hop2Half h D) (q + 1))) ∧
      (∀ x, keyOf hd x ≠ none → keyOf hd x ≠ some D → C x = B x) ∧
      KeepKey hd B C {B (colCell k s (hop2Half h D) 0)} ∧
      keyOf hd (position C (B (colCell k s (hop2Half h D) 0))) = some D ∧
      p.inefficientMoves ≤ 2 * s + 14 * (k + 2) + 7 * (k + 2) * k +
        ((Finset.range (hop2Pos s h D + 1)).filter fun q =>
          classOf hd (B (colCell k s (hop2Half h D) q)) ≠ D).card := by
  set V := hop2Half h D with hV
  set P := hop2Pos s h D with hP
  obtain ⟨hPl, hPb, hPo⟩ := hop2_geom hd hne
  rw [← hV, ← hP] at hPl hPb hPo
  have hV1 : V.1 = D.2 := rfl
  have hV2 : V.2.1 = D.1 := rfl
  have hV3 : V.2.2 = decide (D.1 < h.1) := rfl
  have hks := hd.k_lt_s
  have hroom := hd.room
  have ha := D.1.isLt
  have hbD1 := hd.band_le D.1.isLt
  have hbD2 := hd.band_le D.2.isLt
  have hm : 0 < s - k := by omega
  obtain ⟨jj, hjj⟩ := hd.even
  -- the cells
  set y0 := colCell (n := n) k s V 0 with hy0
  have y0f := colCell_fst (n := n) hd V 0 (by omega)
  have y0s : y0.2.val = D.2.val * s + D.1.val := colCell_snd hd V 0
  obtain ⟨hz1, hz2⟩ := cBand_zero (k := k) (s := s) V
  obtain ⟨oD, hoD1, hoD2, hoD3⟩ : ∃ oD, k ≤ oD ∧ oD < s ∧
      Nat.dist (D.1.val * s + oD) y0.1.val = k + 1 := by
    rw [y0f, hz1, hz2, hV3, hV2]
    by_cases hl : D.1 < h.1
    · refine ⟨s - 1, by omega, by omega, ?_⟩
      simp only [hl, decide_true, if_true, add_one_mul, Nat.dist]; omega
    · have hl' : h.1.val < D.1.val := by
        have : ¬ D.1.val < h.1.val := hl
        have : h.1.val ≠ D.1.val := fun e => hne (Fin.ext e)
        omega
      refine ⟨k, le_rfl, by omega, ?_⟩
      have : (D.1.val - 1) * s + s = D.1.val * s := by
        rw [← add_one_mul]; congr 1; omega
      simp only [hl, decide_false, Bool.false_eq_true, if_false, Nat.dist]; omega
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + D.1.val + jp) % 2 = 1 :=
    ⟨if (k + D.1.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  let e0 : Cell n := mkCell n (D.1.val * s + oD) (D.2.val * s + k + jp)
  have e0f : e0.1.val = D.1.val * s + oD := mkCell_fst (by omega)
  have e0s : e0.2.val = D.2.val * s + k + jp := mkCell_snd (by omega)
  have he0 : reservoir k s D e0 := (reservoir_iff hd).mpr (by omega)
  let x1 : Cell n := mkCell n (D.1.val * s + oD) (D.2.val * s + D.1.val)
  have x1f : x1.1.val = D.1.val * s + oD := mkCell_fst (by omega)
  have x1s : x1.2.val = D.2.val * s + D.1.val := mkCell_snd (by omega)
  have hkx1 : keyOf hd x1 = some D :=
    keyOf_coords_some hd x1f x1s hoD2 (by omega) (Or.inr ⟨hoD1, Or.inr rfl⟩)
  have hky0 : keyOf hd y0 = none := keyOf_colCell hd V 0 (by omega)
  have hx1y0 : x1 ≠ y0 := ne_of_keyOf (by rw [hkx1, hky0]; simp)
  -- A: walk
  obtain ⟨B1, p1, hbB1, hl1, hf1⟩ := exists_reservoir_walk hd B hbl he0
  -- B: horizontal jump onto the own column piece
  obtain ⟨p2, hp2⟩ := exists_hjump_step hd.two_le_n B1 x1
    (by rw [hbB1, e0f, x1f]; simp [Nat.dist]) (by rw [hbB1, e0f, e0s, x1f, x1s]; omega)
  let B2 := swapCells B1 (blank B1) x1
  have hbB2 : blank B2 = x1 := blank_swapCells B1 _
  have hB2 : ∀ x, ¬ reservoir k s D x → x ≠ x1 → B2 x = B x := by
    intro x h1 h2
    change swapCells B1 (blank B1) x1 x = B x
    rw [swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ he0)) h2, hf1 x h1]
  -- C: vertical jump across the row group
  obtain ⟨p3, hp3⟩ := exists_vjump_step hd.two_le_n B2 y0
    (by rw [hbB2, x1s, y0s]; simp [Nat.dist])
    (by rw [hbB2, x1f, x1s, y0s]; unfold Nat.dist at hoD3; omega)
  let B3 := swapCells B2 (blank B2) y0
  have hbB3 : blank B3 = y0 := blank_swapCells B2 _
  have hB3 : ∀ x, keyOf hd x = none → x ≠ y0 → B3 x = B x := by
    intro x hx h2
    change swapCells B2 (blank B2) y0 x = B x
    rw [swapCells_preserves B2 (by rw [hbB2]; exact ne_of_keyOf (by rw [hx, hkx1]; simp)) h2]
    apply hB2
    · exact fun hr => by rw [keyOf_reservoir hd hr] at hx; cases hx
    · exact ne_of_keyOf (by rw [hx, hkx1]; simp)
  -- D: the column walk
  let f : ℕ → Cell n := fun t => colCell k s V t
  have hkf : ∀ t, t ≤ P → keyOf hd (f t) = none := fun t ht => keyOf_colCell hd V t (by omega)
  obtain ⟨B4, p4, hbB4, hC4, hfix4, hi4⟩ := exists_swap_walk P f
    (fun t T => if (t + 1) % (s - k) = 0 then 7 * (k + 2) else moveCost (f t) (f (t + 1)) T)
    (fun t t' ht ht' e => (colCell_inj hd (by omega) (by omega) e).2)
    (fun t ht B' hB' => by
      obtain ⟨hcol, hcase⟩ := colCell_step (n := n) hd V t (by omega)
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · obtain ⟨q, hq⟩ := exists_vjump_step hd.two_le_n B' (f (t + 1))
          (by rw [hB']; simp [f, hcol])
          (by
            rw [hB']
            have := congrArg Fin.val hcol
            unfold Nat.dist at h2
            simp only [f] at this ⊢
            omega)
        refine ⟨q, hq.trans ?_⟩
        rw [if_pos h1, hB']
        simp only [f] at h2 ⊢
        rw [h2]
      · obtain ⟨q, hq⟩ := exists_move_step B' (f (t + 1)) (by
          rw [hB']
          have := congrArg Fin.val hcol
          simp only [gridDistance, f, Nat.dist] at this ⊢
          cases e : V.2.2
          · have := h3 e; omega
          · have := h2 e; omega)
        exact ⟨q, hq.trans (by rw [if_neg h1, hB'])⟩)
    B3 hbB3
  have hB3f : ∀ t, 1 ≤ t → t ≤ P → B3 (f t) = B (f t) := fun t h1 h2 =>
    hB3 _ (hkf t h2) (fun e => by have := (colCell_inj hd (by omega) (by omega) e).2; omega)
  set head := B y0 with hhead
  have hB3x1 : B3 x1 = head := by
    change swapCells B2 (blank B2) y0 x1 = B y0
    rw [← hbB2, swapCells_at_left, hB2 y0 (fun hr => by rw [keyOf_reservoir hd hr] at hky0; cases hky0)
      hx1y0.symm]
  have offl : ∀ x, keyOf hd x ≠ none → ∀ t, t ≤ P → x ≠ f t :=
    fun x hx t ht e => hx (by rw [e]; exact hkf t ht)
  refine ⟨B4, ((p1.append p2).append p3).append p4, hbB4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hq
    rw [hfix4 x (fun t ht => hq t ht), hB3 x hx (hq 0 (Nat.zero_le _))]
  · intro q hq
    rw [hC4 q hq]
    exact hB3f (q + 1) (by omega) (by omega)
  · intro x h1 h2
    rw [hfix4 x (offl x h1)]
    change swapCells B2 (blank B2) y0 x = B x
    rw [swapCells_preserves B2 (by rw [hbB2]; exact ne_of_keyOf (by rw [hkx1]; exact h2))
      (fun e => h1 (by rw [e]; exact hky0))]
    exact hB2 x (fun hr => h2 (keyOf_reservoir hd hr)) (ne_of_keyOf (by rw [hkx1]; exact h2))
  · have K1 : KeepKey hd B B1 ∅ := keepKey_of_agree hd (reservoir k s D)
      (fun x y hx hy => by rw [keyOf_reservoir hd hx, keyOf_reservoir hd hy]) hf1
    have K2 : KeepKey hd B1 B2 ∅ := keepKey_of_agree hd (fun x => x = e0 ∨ x = x1)
      (fun x y hx hy => by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp only [keyOf_reservoir hd he0, hkx1])
      (fun x hx => by
        simp only [not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    have K3 : KeepKey hd B2 B3 {0, head} := by
      have := keepKey_of_agree_outside hd (B := B2) (C := B3) {x1, y0}
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          exact swapCells_preserves B2 (by rw [hbB2]; exact hx.1) hx.2)
      rwa [Finset.image_insert, Finset.image_singleton, ← hbB2, apply_blank,
        hB2 y0 (fun hr => by rw [keyOf_reservoir hd hr] at hky0; cases hky0) hx1y0.symm]
        at this
    have K4 : KeepKey hd B3 B4 ∅ := keepKey_of_agree hd (fun x => keyOf hd x = none)
      (fun x y hx hy => by rw [hx, hy])
      (fun x hx => hfix4 x (offl x hx))
    have K := ((K1.trans K2).trans K3).trans K4
    intro t ht0 htm
    rw [Finset.mem_singleton] at htm
    apply K t ht0
    simp only [Finset.empty_union, Finset.union_empty, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨fun e => ht0 (by rw [e]; rfl), htm⟩
  · have : B4 x1 = head := by
      rw [hfix4 x1 (offl x1 (by rw [hkx1]; simp)), hB3x1]
    rw [position_eq_of_apply this, hkx1]
  · -- cost
    simp only [Path.inefficientMoves_append]
    have c1 := p1.inefficientMoves_le_length
    have c2 : 7 * (Nat.dist (blank B1).2.val x1.2.val + 1) ≤ 7 * (k + 2) := by
      rw [hbB1, e0s, x1s]; simp only [Nat.dist]; omega
    have c3 : 7 * (Nat.dist (blank B2).1.val y0.1.val + 1) ≤ 7 * (k + 2) := by
      rw [hbB2, x1f]; rw [hoD3]
    have hterm : ∀ t ∈ Finset.range P,
        (if (t + 1) % (s - k) = 0 then 7 * (k + 2) else moveCost (f t) (f (t + 1)) (B3 (f (t + 1))))
          ≤ 7 * (k + 2) * (if (s - k) ∣ t + 1 then 1 else 0) +
            (if classOf hd (B (f (t + 1))) ≠ D then 1 else 0) := by
      intro t ht
      rw [Finset.mem_range] at ht
      rw [hB3f (t + 1) (by omega) (by omega)]
      by_cases h1 : (t + 1) % (s - k) = 0
      · rw [if_pos h1, if_pos (Nat.dvd_of_mod_eq_zero h1)]; omega
      · rw [if_neg h1, if_neg (fun h' => h1 (Nat.mod_eq_zero_of_dvd h'))]
        split_ifs with h3
        · have := moveCost_le_one (f t) (f (t + 1)) (B (f (t + 1))); omega
        · push Not at h3
          rw [moveCost_colCell (n := n) hd V t (by omega) h1 _ (by rw [h3]; exact hV2.symm)]
          simp
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
      Nat.card_multiples] at hsum
    have hdivk : P / (s - k) ≤ k := by
      apply Nat.div_le_of_le_mul
      have : colLen k s V ≤ k * (s - k) := by
        unfold colLen; split_ifs
        · exact Nat.mul_le_mul_right _ (by omega)
        · exact Nat.mul_le_mul_right _ (by omega)
      rw [mul_comm]; omega
    have hj : ∑ t ∈ Finset.range P, (if classOf hd (B (f (t + 1))) ≠ D then 1 else 0) ≤
        ((Finset.range (P + 1)).filter fun q => classOf hd (B (colCell k s V q)) ≠ D).card := by
      rw [Finset.card_filter, Finset.sum_range_succ']
      exact Nat.le_add_right _ _
    have hmul : 7 * (k + 2) * (P / (s - k)) ≤ 7 * (k + 2) * k := Nat.mul_le_mul_left _ hdivk
    omega

/-- The corner of the hub's box used by the insertion of a hop2: top left when
the column half leaves upwards, bottom left otherwise. -/
theorem hop2_cornerDist (hd : HDims n k s) {h D : Sq k} {v w : Cell n} (top : Bool) {jp : ℕ}
    (vf : v.1.val = h.1.val * s + (if top then k else s - 1))
    (vs : v.2.val = h.2.val * s + D.1.val) (wf : w.1.val = v.1.val)
    (ws : w.2.val = h.2.val * s + k + jp) (hjp : jp ≤ 1) :
    ∀ j, j ≤ 2 → cornerDist (h.1.val * s) (h.2.val * s) s (!top) false w v
      (mkCell n (h.1.val * s + (if top then k + 2 else s - 3)) (h.2.val * s + k + j)) ≤
        6 * k + 7 := by
  intro j hj
  have hroom := hd.room
  have hb1 := hd.band_le h.1.isLt
  have hb2 := hd.band_le h.2.isLt
  have ha := D.1.isLt
  cases top
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true] at vf ⊢
    unfold cornerDist reflC
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [mkCell_fst (by omega), mkCell_snd (by omega), wf, ws, vf, vs]
    simp only [Nat.dist]
    omega

/-- hop2 realized on the board. -/
theorem simulate_hop2 (hd : HDims n k s) {B : Board n} {σ : IState k} (hR : Rel hd B σ)
    {h D y : Sq k} (hpre : σ.Pre (.hop2 h D y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel hd C (σ.step s (.hop2 h D y)) ∧
      p.inefficientMoves ≤ σ.cost s (.hop2 h D y) := by
  obtain ⟨hbl, hc2, hne, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl⟩ := hR
  rw [hbl] at hRbl
  set V := hop2Half h D with hV
  set P := hop2Pos s h D with hP
  obtain ⟨hPl, hPb, hPo⟩ := hop2_geom hd hne
  rw [← hV, ← hP] at hPl hPb hPo
  obtain ⟨B4, p4, hb4, hA, hBcol, hBreg, K1, hkhead, hi4⟩ := hop2_phase1 hd B hRbl hne
  rw [← hP] at hi4
  have hV1 : V.1 = D.2 := rfl
  have hV2 : V.2.1 = D.1 := rfl
  have hhD : h ≠ D := fun e => hne (by rw [e])
  have hks := hd.k_lt_s
  have hroom := hd.room
  have ha := D.1.isLt
  have hbh1 := hd.band_le h.1.isLt
  have hbh2 := hd.band_le h.2.isLt
  have e2 : D.2.val * s = h.2.val * s := by rw [hc2]
  -- the insertion cell and the jump target
  set v := colCell (n := n) k s V P with hv
  have vf : v.1.val = cBand k s V P * s + cOff k s V P := colCell_fst hd V P hPl
  have vs : v.2.val = D.2.val * s + D.1.val := colCell_snd hd V P
  rw [hPb] at vf
  obtain ⟨oh, hoh1, hoh2, hoh3, hoh4⟩ : ∃ oh, k ≤ oh ∧ oh < s ∧ oh ≠ k + 2 ∧
      v.1.val = h.1.val * s + oh := by
    refine ⟨cOff k s V P, ?_, ?_, ?_, vf⟩ <;> rw [hPo] <;> split_ifs <;> omega
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + D.1.val + jp) % 2 = 1 :=
    ⟨if (k + D.1.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  let w : Cell n := mkCell n v.1.val (h.2.val * s + k + jp)
  have wf : w.1.val = v.1.val := mkCell_fst v.1.isLt
  have ws : w.2.val = h.2.val * s + k + jp := mkCell_snd (by omega)
  have hw : reservoir k s h w := (reservoir_iff hd).mpr (by omega)
  have hkv : keyOf hd v = none := keyOf_colCell hd V P hPl
  have hvbox : InBox (h.1.val * s) (h.2.val * s) s v := by
    unfold InBox; omega
  have hreg4 : ∀ x, region k s h x → B4 x = B x := fun x hx =>
    hBreg x (by rw [(keyOf_eq_some hd).mpr hx]; simp)
      (by rw [(keyOf_eq_some hd).mpr hx]; exact fun e => hhD (Option.some.inj e))
  have hT4 : 1 ≤ regionCount hd B4 h y := by
    rw [regionCount_congr hd hreg4, hRcnt]; exact hcnt
  obtain ⟨p5, hp5⟩ := exists_hjump_step hd.two_le_n B4 w
    (by rw [hb4, wf]; simp [Nat.dist]) (by rw [hb4, wf, ws, vs]; omega)
  have hvf : v.1.val = h.1.val * s + (if decide (D.1 < h.1) then k else s - 1) := by
    rw [vf, hPo]; simp only [decide_eq_true_eq]
  have hD := hop2_cornerDist hd (D := D) (decide (D.1 < h.1)) hvf (by rw [vs, hc2]) wf ws hjp1
  obtain ⟨C, p6, T, hT0, hTc, hTk, hCv, hCbl, hCx, K2, hi6⟩ :=
    insert_by_cycle hd B4 (Q := h) (y := y) hb4 hkv hw hvbox hT4
      (7 * (k + 2)) ⟨p5, hp5.trans (by rw [hb4, ws, vs]; simp only [Nat.dist]; omega)⟩
      (!decide (D.1 < h.1)) false (ro := if decide (D.1 < h.1) then k + 2 else s - 3) (co := k)
      (by split_ifs <;> omega) (by split_ifs <;> omega) le_rfl (by omega) hD
  have hCc : ∀ x, keyOf hd x = none → x ≠ v → C x = B4 x := fun x hx hxv =>
    hCx x hxv (by rw [hx]; simp)
  set head := B (colCell k s V 0) with hhead
  have hhead0 : head.val ≠ 0 := (hRcol V 0 (by omega)).1
  have hkB4T : keyOf hd (position B4 T) = some h := hTk
  have hTh : head ≠ T := by
    intro e
    rw [← e, hkhead] at hkB4T
    exact hhD (Option.some.inj hkB4T).symm
  refine ⟨C, p4.append p6, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- row halves
    intro H q hq
    simp only [IState.step]
    have hk := keyOf_rowCell (n := n) hd H q hq
    rw [hCc _ hk (fun e => rowCell_ne_colCell hd H V q P hPl e),
      hA _ hk (fun q' hq' e => rowCell_ne_colCell hd H V q q' (by omega) e)]
    exact hRrow H q hq
  · -- column halves
    intro V' q' hq'
    simp only [IState.step]
    by_cases e : V' = V ∧ q' ≤ P
    · obtain ⟨rfl, hq'p⟩ := e
      rw [Function.update_self]
      unfold shiftIn
      rcases Nat.lt_or_ge q' P with hlt | hge
      · rw [if_pos hlt, hCc _ (keyOf_colCell hd V q' hq')
          (fun e => by have := (colCell_inj hd hq' hPl e).2; omega), hBcol q' hlt]
        exact hRcol V (q' + 1) (by omega)
      · have hq : q' = P := by omega
        subst hq
        rw [if_neg (lt_irrefl _), if_pos rfl, hCv, hTc]
        exact ⟨hT0, rfl⟩
    · have hne' : ∀ q, q ≤ P → colCell (n := n) k s V' q' ≠ colCell k s V q := by
        intro q hq e'
        obtain ⟨h1, h2⟩ := colCell_inj hd hq' (by omega) e'
        exact e ⟨h1, by omega⟩
      rw [hCc _ (keyOf_colCell hd V' q' hq') (hne' P le_rfl),
        hA _ (keyOf_colCell hd V' q' hq') hne']
      by_cases eV : V' = V
      · subst eV
        rw [Function.update_self]
        unfold shiftIn
        have : ¬ q' ≤ P := fun hh => e ⟨rfl, hh⟩
        rw [if_neg (by omega), if_neg (by omega)]
        exact hRcol V q' hq'
      · rw [Function.update_of_ne eV]
        exact hRcol V' q' hq'
  · -- region counts
    intro Q y'
    simp only [IState.step]
    have K : KeepKey hd B C {head, T} := by
      have := K1.trans K2
      rwa [← Finset.insert_eq] at this
    have k1C : keyOf hd (position C head) = some D := by
      rw [K2 head hhead0 (by simpa using hTh), hkhead]
    have k2B : keyOf hd (position B T) = some h := by
      rw [← K1 T hT0 (by simpa using hTh.symm)]; exact hkB4T
    have k1B : keyOf hd (position B head) = none := by
      rw [show position B head = colCell k s V 0 by simp [hhead, position]]
      exact keyOf_colCell hd V 0 (by omega)
    have k2C : keyOf hd (position C T) = none := by
      rw [position_eq_of_apply hCv]; exact hkv
    rw [regionCount_move2 hd K hTh hhead0 hT0 hhD k1B k1C k2B k2C Q y', hTc,
      (hRcol V 0 (by omega)).2]
    have hc : regionCount hd B = σ.cnt := funext fun Q => funext fun y => hRcnt Q y
    rw [hc]
  · -- the blank
    simp only [IState.step]
    rw [hCbl]; exact hw
  · -- cost
    simp only [IState.cost, IState.junkCol]
    rw [Path.inefficientMoves_append]
    have hj : ((Finset.range (P + 1)).filter fun q => classOf hd (B (colCell k s V q)) ≠ D) =
        ((Finset.range (P + 1)).filter fun q => σ.col V q ≠ (V.2.1, V.1)) := by
      apply Finset.filter_congr
      intro q hq
      rw [Finset.mem_range] at hq
      rw [(hRcol V q (by omega)).2]
      exact Iff.rfl
    rw [hj] at hi4
    change _ ≤ 12 * s + 7 * k ^ 2 + 527 * k + 1052 +
      ((Finset.range (P + 1)).filter fun q => σ.col V q ≠ (V.2.1, V.1)).card
    have e1 : 7 * (k + 2) * k = 7 * (k * k) + 14 * k := by ring
    have e3 : k ^ 2 = k * k := sq k
    have hk2 := hd.two_le
    have hk4 : 4 ≤ k ^ 2 := by nlinarith
    omega

end SlidingPuzzle.Hub
