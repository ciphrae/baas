import SlidingPuzzle.Tree.GeomCol

/-! # hopC: along a column lane, into its landing square

Phase 1: the blank walks inside the landing square `D`'s reservoir, jumps
horizontally onto `D`'s own column piece, jumps vertically into position `0`
of the lane (the head drops into `D`'s region) and walks along the lane to the
insertion position `p` (adjacent steps inside a band, jumps of `q + 1` between
bands). Phase 2 (`insert_by_cycle`) jumps into the source's reservoir and places
the inserted tile at `p`. -/
namespace SlidingPuzzle.Tree
open Classical
open SlidingPuzzle.Hub

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

/-- Phase 1 of a column hop. -/
theorem hopC_phase1 (td : TDims n k s q) (B : Board n) {V : LaneI k q} {I : Fin k}
    (hI : LIn L V I) (hbl : reservoir k s (colLand V) (blank B)) :
    ∃ C : Board n, ∃ p : Path B C,
      blank C = colCell s V (colPos k s q V I) ∧
      (∀ x, key L td.hd x = none → (∀ r, r ≤ colPos k s q V I → x ≠ colCell s V r) →
        C x = B x) ∧
      (∀ r, r < colPos k s q V I → C (colCell s V r) = B (colCell s V (r + 1))) ∧
      (∀ x, key L td.hd x ≠ none → key L td.hd x ≠ some (colLand V) → C x = B x) ∧
      KeepKey L td.hd B C {B (colCell s V 0)} ∧
      key L td.hd (position C (B (colCell s V 0))) = some (colLand V) ∧
      p.inefficientMoves ≤ 2 * s + 14 * (k + 2) + 7 * (q + 2) * k +
        ((Finset.range (colPos k s q V I + 1)).filter fun r =>
          ¬ colGood V (classOf td.hd (B (colCell s V r)))).card := by
  set D := colLand V with hDdef
  set P := colPos k s q V I with hP
  obtain ⟨hPl, -, -⟩ := colPos_geom L td V I hI
  rw [← hP] at hPl
  have hpos := blen_pos_of_in L hI
  have hks := td.k_lt_s
  have hroom := td.hd.room
  have hqk := td.q_le
  have hqs := td.q_lt_s
  have ho := V.o.isLt
  have hbD1 := td.band_le V.t.isLt
  have hbD2 := td.band_le V.b.isLt
  have hm : 0 < s - q := by omega
  obtain ⟨jj, hjj⟩ := td.hd.even
  obtain ⟨qq, hqq⟩ := td.even_q
  have hbs := blen_side L V
  -- the cells
  set y0 := colCell (n := n) s V 0 with hy0
  have y0f := colCell_fst (n := n) L td V 0 (by omega)
  have y0s : y0.2.val = V.b.val * s + V.o.val := colCell_snd td V 0
  obtain ⟨hz1, hz2⟩ := cBand_zero (k := k) (s := s) (q := q) V
  obtain ⟨oD, hoD1, hoD2, hoD3, hoD4⟩ : ∃ oD, k ≤ oD ∧ oD < s ∧
      Nat.dist (V.t.val * s + oD) y0.1.val ≤ k + 1 ∧
      (V.t.val * s + oD + y0.1.val) % 2 = 1 := by
    rw [y0f, hz1, hz2]
    cases hsd : V.side
    · have ht1 : 1 ≤ V.t.val := by have := hbs.2 hsd; omega
      have : (V.t.val - 1) * s + s = V.t.val * s := by
        rw [← add_one_mul]; congr 1; omega
      refine ⟨k, le_rfl, by omega, ?_, ?_⟩
      · simp only [Bool.false_eq_true, if_false, Nat.dist]; omega
      · simp only [Bool.false_eq_true, if_false]; omega
    · refine ⟨s - 1, by omega, by omega, ?_, ?_⟩
      · simp only [if_true, add_one_mul, Nat.dist]; omega
      · simp only [if_true, add_one_mul]; omega
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + V.o.val + jp) % 2 = 1 :=
    ⟨if (k + V.o.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  let e0 : Cell n := mkCell n (V.t.val * s + oD) (V.b.val * s + k + jp)
  have e0f : e0.1.val = V.t.val * s + oD := mkCell_fst (by omega)
  have e0s : e0.2.val = V.b.val * s + k + jp := mkCell_snd (by omega)
  have he0 : reservoir k s D e0 := (reservoir_iff td.hd).mpr (by simp only [hDdef, colLand]; omega)
  let x1 : Cell n := mkCell n (V.t.val * s + oD) (V.b.val * s + V.o.val)
  have x1f : x1.1.val = V.t.val * s + oD := mkCell_fst (by omega)
  have x1s : x1.2.val = V.b.val * s + V.o.val := mkCell_snd (by omega)
  have hkx1 : key L td.hd x1 = some D :=
    (key_eq_some L td.hd).mpr (region_ownCol L td V hpos x1f (by omega) hoD2 x1s)
  have hky0 : key L td.hd y0 = none := key_colCell L td V 0 (by omega)
  have hx1y0 : x1 ≠ y0 := ne_of_key L (by rw [hkx1, hky0]; simp)
  -- A: walk
  obtain ⟨B1, p1, hbB1, hl1, hf1, -⟩ := exists_reservoir_walk td.hd B hbl he0
  -- B: horizontal jump onto the own column piece
  obtain ⟨p2, hp2⟩ := exists_hjump_step td.hd.two_le_n B1 x1
    (by rw [hbB1, e0f, x1f]; simp [Nat.dist]) (by rw [hbB1, e0f, e0s, x1f, x1s]; omega)
  let B2 := swapCells B1 (blank B1) x1
  have hbB2 : blank B2 = x1 := blank_swapCells B1 _
  have hB2 : ∀ x, ¬ reservoir k s D x → x ≠ x1 → B2 x = B x := by
    intro x h1 h2
    change swapCells B1 (blank B1) x1 x = B x
    rw [swapCells_preserves B1 (by rw [hbB1]; exact fun e => h1 (e ▸ he0)) h2, hf1 x h1]
  -- C: vertical jump into position `0`
  obtain ⟨p3, hp3⟩ := exists_vjump_step td.hd.two_le_n B2 y0
    (by rw [hbB2, x1s, y0s]; simp [Nat.dist])
    (by rw [hbB2, x1f, x1s, y0s]; omega)
  let B3 := swapCells B2 (blank B2) y0
  have hbB3 : blank B3 = y0 := blank_swapCells B2 _
  have hB3 : ∀ x, key L td.hd x = none → x ≠ y0 → B3 x = B x := by
    intro x hx h2
    change swapCells B2 (blank B2) y0 x = B x
    rw [swapCells_preserves B2 (by rw [hbB2]; exact ne_of_key L (by rw [hx, hkx1]; simp)) h2]
    apply hB2
    · exact fun hr => by rw [key_reservoir L td hr] at hx; cases hx
    · exact ne_of_key L (by rw [hx, hkx1]; simp)
  -- D: the column walk
  let f : ℕ → Cell n := fun t => colCell s V t
  have hkf : ∀ t, t ≤ P → key L td.hd (f t) = none := fun t ht => key_colCell L td V t (by omega)
  obtain ⟨B4, p4, hbB4, hC4, hfix4, hi4⟩ := exists_swap_walk P f
    (fun t T => if (t + 1) % (s - q) = 0 then 7 * (q + 2) else moveCost (f t) (f (t + 1)) T)
    (fun t t' ht ht' e => (colCell_inj L td (by omega) (by omega) e).2)
    (fun t ht B' hB' => by
      obtain ⟨hcol, hcase⟩ := colCell_step (n := n) L td V t (by omega)
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · obtain ⟨r, hr⟩ := exists_vjump_step td.hd.two_le_n B' (f (t + 1))
          (by rw [hB']; simp [f, hcol])
          (by
            rw [hB']
            have := congrArg Fin.val hcol
            unfold Nat.dist at h2
            simp only [f] at this ⊢
            omega)
        refine ⟨r, hr.trans ?_⟩
        rw [if_pos h1, hB']
        simp only [f] at h2 ⊢
        rw [h2]
      · obtain ⟨r, hr⟩ := exists_move_step B' (f (t + 1)) (by
          rw [hB']
          have := congrArg Fin.val hcol
          simp only [gridDistance, f, Nat.dist] at this ⊢
          cases e : V.side
          · have := h3 e; omega
          · have := h2 e; omega)
        exact ⟨r, hr.trans (by rw [if_neg h1, hB'])⟩)
    B3 hbB3
  have hB3f : ∀ t, 1 ≤ t → t ≤ P → B3 (f t) = B (f t) := fun t h1 h2 =>
    hB3 _ (hkf t h2) (fun e => by have := (colCell_inj L td (by omega) (by omega) e).2; omega)
  set head := B y0 with hhead
  have hB3x1 : B3 x1 = head := by
    change swapCells B2 (blank B2) y0 x1 = B y0
    rw [← hbB2, swapCells_at_left,
      hB2 y0 (fun hr => by rw [key_reservoir L td hr] at hky0; cases hky0) hx1y0.symm]
  have offl : ∀ x, key L td.hd x ≠ none → ∀ t, t ≤ P → x ≠ f t :=
    fun x hx t ht e => hx (by rw [e]; exact hkf t ht)
  refine ⟨B4, ((p1.append p2).append p3).append p4, hbB4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hq
    rw [hfix4 x (fun t ht => hq t ht), hB3 x hx (hq 0 (Nat.zero_le _))]
  · intro r hr
    rw [hC4 r hr]
    exact hB3f (r + 1) (by omega) (by omega)
  · intro x h1 h2
    rw [hfix4 x (offl x h1)]
    change swapCells B2 (blank B2) y0 x = B x
    rw [swapCells_preserves B2 (by rw [hbB2]; exact ne_of_key L (by rw [hkx1]; exact h2))
      (fun e => h1 (by rw [e]; exact hky0))]
    exact hB2 x (fun hr => h2 (key_reservoir L td hr)) (ne_of_key L (by rw [hkx1]; exact h2))
  · have K1 : KeepKey L td.hd B B1 ∅ := keepKey_of_agree L td.hd (reservoir k s D)
      (fun x y hx hy => by rw [key_reservoir L td hx, key_reservoir L td hy]) hf1
    have K2 : KeepKey L td.hd B1 B2 ∅ := keepKey_of_agree L td.hd (fun x => x = e0 ∨ x = x1)
      (fun x y hx hy => by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp only [key_reservoir L td he0, hkx1])
      (fun x hx => by
        simp only [not_or] at hx
        exact swapCells_preserves B1 (by rw [hbB1]; exact hx.1) hx.2)
    have K3 : KeepKey L td.hd B2 B3 {0, head} := by
      have := keepKey_of_agree_outside L td.hd (B := B2) (C := B3) {x1, y0}
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          exact swapCells_preserves B2 (by rw [hbB2]; exact hx.1) hx.2)
      rwa [Finset.image_insert, Finset.image_singleton, ← hbB2, apply_blank,
        hB2 y0 (fun hr => by rw [key_reservoir L td hr] at hky0; cases hky0) hx1y0.symm]
        at this
    have K4 : KeepKey L td.hd B3 B4 ∅ := keepKey_of_agree L td.hd (fun x => key L td.hd x = none)
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
      rw [hbB2, x1f]; omega
    have hterm : ∀ t ∈ Finset.range P,
        (if (t + 1) % (s - q) = 0 then 7 * (q + 2)
          else moveCost (f t) (f (t + 1)) (B3 (f (t + 1))))
          ≤ 7 * (q + 2) * (if (s - q) ∣ t + 1 then 1 else 0) +
            (if ¬ colGood V (classOf td.hd (B (f (t + 1)))) then 1 else 0) := by
      intro t ht
      rw [Finset.mem_range] at ht
      rw [hB3f (t + 1) (by omega) (by omega)]
      by_cases h1 : (t + 1) % (s - q) = 0
      · rw [if_pos h1, if_pos (Nat.dvd_of_mod_eq_zero h1)]; omega
      · rw [if_neg h1, if_neg (fun h' => h1 (Nat.mod_eq_zero_of_dvd h'))]
        by_cases hg : colGood V (classOf td.hd (B (f (t + 1))))
        · rw [moveCost_colCell (n := n) L td V t (by omega) h1 _ hg]; simp
        · rw [if_pos hg]; have := moveCost_le_one (f t) (f (t + 1)) (B (f (t + 1))); omega
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
      Nat.card_multiples] at hsum
    have hdivk : P / (s - q) ≤ k := by
      apply Nat.div_le_of_le_mul
      have : colLen L s V ≤ k * (s - q) := by
        unfold colLen
        apply Nat.mul_le_mul_right
        have := V.t.isLt
        cases e : V.side
        · have := hbs.2 e; omega
        · have := hbs.1 e; omega
      rw [mul_comm]; omega
    have hj : ∑ t ∈ Finset.range P, (if ¬ colGood V (classOf td.hd (B (f (t + 1)))) then 1 else 0)
        ≤ ((Finset.range (P + 1)).filter fun r =>
          ¬ colGood V (classOf td.hd (B (colCell s V r)))).card := by
      rw [Finset.card_filter, Finset.sum_range_succ']
      exact Nat.le_add_right _ _
    have hmul : 7 * (q + 2) * (P / (s - q)) ≤ 7 * (q + 2) * k := Nat.mul_le_mul_left _ hdivk
    omega

/-- The corner of the source's box used by the insertion of a column hop: top
left for lanes after the landing band, bottom left otherwise. -/
theorem hopC_cornerDist (td : TDims n k s q) {S : Sq k} {V : LaneI k q} {v w : Cell n}
    (top : Bool) {jp : ℕ}
    (vf : v.1.val = S.1.val * s + (if top then k else s - 1))
    (vs : v.2.val = S.2.val * s + V.o.val) (wf : w.1.val = v.1.val)
    (ws : w.2.val = S.2.val * s + k + jp) (hjp : jp ≤ 1) :
    ∀ j, j ≤ 2 → cornerDist (S.1.val * s) (S.2.val * s) s (!top) false w v
      (mkCell n (S.1.val * s + (if top then k + 2 else s - 3)) (S.2.val * s + k + j)) ≤
        6 * k + 7 := by
  intro j hj
  have hroom := td.hd.room
  have hb1 := td.band_le S.1.isLt
  have hb2 := td.band_le S.2.isLt
  have ho := V.o.isLt
  have hqk := td.q_le
  cases top
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true] at vf ⊢
    unfold cornerDist reflC
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [mkCell_fst (by omega), mkCell_snd (by omega), wf, ws, vf, vs]
    simp only [Nat.dist]
    omega

/-- A column hop realized on the board. -/
theorem simulate_hopC (td : TDims n k s q) {B : Board n} {σ : IState k q} (hR : Rel L td.hd B σ)
    {V : LaneI k q} {I : Fin k} {y : Sq k} (hpre : σ.Pre L (.hopC V I y)) :
    ∃ C : Board n, ∃ p : Path B C, Rel L td.hd C (σ.step s (.hopC V I y)) ∧
      p.inefficientMoves ≤ σ.cost s (.hopC V I y) := by
  obtain ⟨hbl, hI, hcnt⟩ := hpre
  obtain ⟨hRrow, hRcol, hRcnt, hRbl⟩ := hR
  rw [hbl] at hRbl
  set S : Sq k := (I, V.b) with hSdef
  set D := colLand V with hDdef
  set P := colPos k s q V I with hP
  obtain ⟨hPl, hPb, hPo⟩ := colPos_geom L td V I hI
  rw [← hP] at hPl hPb hPo
  obtain ⟨B4, p4, hb4, hA, hBcol, hBreg, K1, hkhead, hi4⟩ := hopC_phase1 L td B hI hRbl
  rw [← hP] at hi4
  have hSD : S ≠ D := by
    intro e
    have := congrArg Prod.fst e
    simp only [hSdef, hDdef, colLand] at this
    have hne := LaneSys.inPiece_lt hI
    rcases hne with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [this] at h' <;> omega
  have hks := td.k_lt_s
  have hroom := td.hd.room
  have hqk := td.q_le
  have ho := V.o.isLt
  have hbh1 := td.band_le I.isLt
  have hbh2 := td.band_le V.b.isLt
  -- the insertion cell and the jump target
  set v := colCell (n := n) s V P with hv
  have vf : v.1.val = cBand s q V P * s + cOff s q V P := colCell_fst L td V P hPl
  have vs : v.2.val = V.b.val * s + V.o.val := colCell_snd td V P
  rw [hPb] at vf
  obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (k + V.o.val + jp) % 2 = 1 :=
    ⟨if (k + V.o.val) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  let w : Cell n := mkCell n v.1.val (V.b.val * s + k + jp)
  have wf : w.1.val = v.1.val := mkCell_fst v.1.isLt
  have ws : w.2.val = V.b.val * s + k + jp := mkCell_snd (by omega)
  have hw : reservoir k s S w := (reservoir_iff td.hd).mpr (by
    simp only [hSdef]; rw [wf, vf, hPo]; split_ifs <;> omega)
  have hkv : key L td.hd v = none := key_colCell L td V P hPl
  have hvbox : InBox (S.1.val * s) (S.2.val * s) s v := by
    unfold InBox; simp only [hSdef]; rw [vf, vs, hPo]; split_ifs <;> omega
  have hreg4 : ∀ x, region L s S x → B4 x = B x := fun x hx =>
    hBreg x (by rw [(key_eq_some L td.hd).mpr hx]; simp)
      (by rw [(key_eq_some L td.hd).mpr hx]; exact fun e => hSD (Option.some.inj e))
  obtain ⟨t, htQ, htT, htc⟩ := exists_of_regionCount L td.hd B4 (Q := S) (y := y) (by
      rw [regionCount_congr L td.hd hreg4, hRcnt]; exact hcnt)
  obtain ⟨p5, hp5⟩ := exists_hjump_step td.hd.two_le_n B4 w
    (by rw [hb4, wf]; simp [Nat.dist]) (by rw [hb4, wf, ws, vs]; omega)
  have hvf : v.1.val = S.1.val * s + (if V.side then k else s - 1) := by
    rw [vf, hPo]
  have hD := hopC_cornerDist td (S := S) (V := V) V.side hvf (by rw [vs]) wf ws hjp1
  obtain ⟨C, p6, T, hT0, hTc, hTk, hCv, hCbl, hCx, hCfp, K2, hi6⟩ :=
    insert_by_cycle L td B4 (Q := S) (y := y) hb4 hkv hw hvbox t htQ htT htc
      (7 * (k + 2)) ⟨p5, hp5.trans (by rw [hb4, ws, vs]; simp only [Nat.dist]; omega)⟩
      (!V.side) false (ro := if V.side then k + 2 else s - 3) (co := k)
      (by split_ifs <;> omega) (by split_ifs <;> omega) le_rfl (by omega) hD
  have hCc : ∀ x, key L td.hd x = none → x ≠ v → C x = B4 x := fun x hx hxv =>
    hCx x hxv (by rw [hx]; simp)
  set head := B (colCell s V 0) with hhead
  have hhead0 : head.val ≠ 0 := (hRcol V 0 (by omega)).1
  have hkB4T : key L td.hd (position B4 T) = some S := hTk
  have hTh : head ≠ T := by
    intro e
    rw [← e, hkhead] at hkB4T
    exact hSD (Option.some.inj hkB4T).symm
  refine ⟨C, p4.append p6, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- row lanes
    intro H r hr
    simp only [IState.step]
    have hk := key_rowCell L td H r hr
    rw [hCc _ hk (fun e => rowCell_ne_colCell L td H V r P hPl e),
      hA _ hk (fun r' hr' e => rowCell_ne_colCell L td H V r r' (by omega) e)]
    exact hRrow H r hr
  · -- column lanes
    intro V' q' hq'
    simp only [IState.step]
    by_cases e : V' = V ∧ q' ≤ P
    · obtain ⟨rfl, hq'p⟩ := e
      rw [Function.update_self]
      unfold shiftIn
      rcases Nat.lt_or_ge q' P with hlt | hge
      · rw [if_pos hlt, hCc _ (key_colCell L td V' q' hq')
          (fun e => by have := (colCell_inj L td hq' hPl e).2; omega), hBcol q' hlt]
        exact hRcol V' (q' + 1) (by omega)
      · have hq : q' = P := by omega
        subst hq
        rw [if_neg (lt_irrefl _), if_pos rfl, hCv, hTc]
        exact ⟨hT0, rfl⟩
    · have hne' : ∀ r, r ≤ P → colCell (n := n) s V' q' ≠ colCell s V r := by
        intro r hr e'
        obtain ⟨h1, h2⟩ := colCell_inj L td hq' (by omega) e'
        exact e ⟨h1, by omega⟩
      rw [hCc _ (key_colCell L td V' q' hq') (hne' P le_rfl),
        hA _ (key_colCell L td V' q' hq') hne']
      by_cases eV : V' = V
      · subst eV
        rw [Function.update_self]
        unfold shiftIn
        have : ¬ q' ≤ P := fun hh => e ⟨rfl, hh⟩
        rw [if_neg (by omega), if_neg (by omega)]
        exact hRcol V' q' hq'
      · rw [Function.update_of_ne eV]
        exact hRcol V' q' hq'
  · -- region counts
    intro Q y'
    simp only [IState.step]
    have K : KeepKey L td.hd B C {head, T} := by
      have := K1.trans K2
      rwa [← Finset.insert_eq] at this
    have k1C : key L td.hd (position C head) = some D := by
      rw [K2 head hhead0 (by simpa using hTh), hkhead]
    have k2B : key L td.hd (position B T) = some S := by
      rw [← K1 T hT0 (by simpa using hTh.symm)]; exact hkB4T
    have k1B : key L td.hd (position B head) = none := by
      rw [show position B head = colCell s V 0 by simp [hhead, position]]
      exact key_colCell L td V 0 (by omega)
    have k2C : key L td.hd (position C T) = none := by
      rw [position_eq_of_apply hCv]; exact hkv
    rw [regionCount_move2 L td.hd K hTh hhead0 hT0 hSD k1B k1C k2B k2C Q y', hTc,
      (hRcol V 0 (by omega)).2]
    have hc : regionCount L td.hd B = σ.cnt := funext fun Q => funext fun y => hRcnt Q y
    rw [hc]
  · -- the blank
    simp only [IState.step]
    rw [hCbl]; exact hw
  · -- cost
    simp only [IState.cost, IState.junkCol]
    rw [Path.inefficientMoves_append]
    have hj : ((Finset.range (P + 1)).filter fun r =>
        ¬ colGood V (classOf td.hd (B (colCell s V r)))) =
        ((Finset.range (P + 1)).filter fun r => ¬ colGood V (σ.col V r)) := by
      apply Finset.filter_congr
      intro r hr
      rw [Finset.mem_range] at hr
      rw [(hRcol V r (by omega)).2]
    rw [hj] at hi4
    change _ ≤ 20 * s + 20 * k * (q + 2) + 600 * k + 2000 +
      ((Finset.range (P + 1)).filter fun r => ¬ colGood V (σ.col V r)).card
    have e1 : 7 * (q + 2) * k ≤ 20 * k * (q + 2) := by nlinarith
    omega

end SlidingPuzzle.Tree
