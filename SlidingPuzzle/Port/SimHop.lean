import SlidingPuzzle.Port.Hop

/-! # The hop event realized on the board -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf shiftIn shiftIn_of_lt shiftIn_self' shiftIn_of_gt
  incCnt decCnt apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

omit [NeZero n] in
theorem step_hop_lane (s : ℕ) (ρ : PState k q) (l : Ln k q) (J : Fin k) (y : Sq k) (m : Mode k) :
    (ρ.step s (.hop l J y m)).lane =
      Function.update ρ.lane l (shiftIn (ρ.lane l) (lposP k s l J) y) := by
  funext l' r
  obtain ⟨a, H⟩ := l
  obtain ⟨a', H'⟩ := l'
  unfold PState.lane
  cases a <;> cases a'
  · simp only [PState.step, Bool.false_eq_true, if_false]
    by_cases h : H' = H
    · subst h; simp [PState.lane]
    · rw [Function.update_of_ne h, Function.update_of_ne (by simp [h])]; rfl
  · simp [PState.step, PState.lane]
  · simp [PState.step, PState.lane]
  · simp only [PState.step, if_true]
    by_cases h : H' = H
    · subst h; simp [PState.lane]
    · rw [Function.update_of_ne h, Function.update_of_ne (by simp [h])]; rfl

/-- `PRel` from its lane form. -/
theorem prel_of_lanes (pd : PDims n k s q σ) {C : Board n} {ρ : PState k q}
    (hl : ∀ l r, r < llen L s l →
      (C (lcell s l r)).val ≠ 0 ∧ classOf pd.hd (C (lcell s l r)) = ρ.lane l r)
    (hc : ∀ Q y, regionCount L pd.hd C Q y = ρ.cnt Q y)
    (hp : ∀ Q pt y, pcount L s σ pd.hd C Q (some pt) y = ρ.pc Q pt y)
    (hb : InBoxOf s σ ρ.blank ρ.bp (blank C)) : PRel L pd C ρ :=
  ⟨fun H p hp' => hl (false, H) p hp', fun V p hp' => hl (true, V) p hp', hc, hp, hb⟩

/-- The effect of a landing on the port counts. -/
theorem pc_landing (pd : PDims n k s q σ) {B C : Board n} {t : Tile n} {D : Sq k} {pt : Pt}
    (K : KeepK (rkey L s σ pd.hd) B C {t}) (ht : t.val ≠ 0)
    (hB : rkey L s σ pd.hd (position B t) = none)
    (hC : rkey L s σ pd.hd (position C t) = some (D, some pt)) :
    pcOf L pd C = incP (pcOf L pd B) D pt (classOf pd.hd t) := by
  funext Q pt' z
  have e := kcount_move1 (rkey L s σ pd.hd) pd.hd K ht (some (Q, some pt')) z
  rw [hB, hC] at e
  unfold pcOf pcount incP
  simp only [reduceCtorEq, false_and, if_false, add_zero, Option.some.injEq, Prod.mk.injEq] at e
  by_cases h : Q = D ∧ pt' = pt ∧ z = classOf pd.hd t
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [and_self, if_true] at e ⊢
    omega
  · rw [if_neg h]
    rw [if_neg (by rintro ⟨⟨h1, h2⟩, h3⟩; exact h ⟨h1.symm, h2.symm, h3.symm⟩)] at e
    omega

/-- A hop realized on the board. -/
theorem simulate_hop (pd : PDims n k s q σ) (h4 : 4 ≤ σ) {B : Board n} {ρ : PState k q}
    (hR : PRel L pd B ρ) {l : Ln k q} {J : Fin k} {y : Sq k} {m : Mode k}
    (hpre : ρ.Pre L (.hop l J y m)) :
    ∃ C : Board n, ∃ p : Path B C, PRel L pd C (ρ.step s (.hop l J y m)) ∧
      p.inefficientMoves ≤ ρ.cost s σ (.hop l J y m) := by
  obtain ⟨hbl, hbp, hJ, hmode⟩ := hpre
  set D := land l with hD
  set S := src l J with hS
  set pt := lport l with hpt
  set P := lposP k s l J with hP
  have hSD : S ≠ D := src_ne_land L hJ
  have hbox : InBoxOf s σ D pt (blank B) := by
    have := hR.2.2.2.2; rw [hbl, hbp] at this; exact this
  obtain ⟨B1, p1, hb1, hlane1, ⟨d, hdk, hB1d, hB1x⟩, K1, hi1⟩ :=
    land_any L pd (by omega) B l J hJ hbox
  obtain ⟨hPl, hvS⟩ := lposP_geom L pd l J hJ
  have h0l : 0 < llen L s l := by omega
  set head := B (lcell s l 0) with hhead
  obtain ⟨hhead0, hheadc⟩ := prel_lane L pd hR l h0l
  -- the source's parts are untouched by the landing
  have hB1S : ∀ x (p' : Part), rkey L s σ pd.hd x = some (S, p') → B1 x = B x := by
    intro x p' hx
    apply hB1x x
    · intro hb
      have := rkey_inBoxOf L pd hb
      rw [hx] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact hSD this.1
    · intro e
      rw [e, hdk] at hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      exact hSD hx.1.symm
    · intro r hr e
      rw [e, rkey_lcell L pd l (by omega)] at hx
      cases hx
  have hpc1 : ∀ (p' : Part) z, pcount L s σ pd.hd B1 S p' z = pcount L s σ pd.hd B S p' z :=
    fun p' z => kcount_congr (rkey L s σ pd.hd) pd.hd (fun x hx => hB1S x p' hx) z
  -- the insertion
  have hv : blank B1 = lc s S (lineRC k s l l.2.o.val).1 (lineRC k s l l.2.o.val).2 := hb1.trans hvS
  have hvk : rkey L s σ pd.hd (blank B1) = none := by rw [hb1]; exact rkey_lcell L pd l hPl
  have hok : InsOK L pd B1 S pt y m := by
    cases m with
    | cheap =>
      show 1 ≤ pcount L s σ pd.hd B1 S (some pt) y
      rw [hpc1, hR.2.2.2.1]; exact hmode
    | imp p z =>
      obtain ⟨h1, h2, h3⟩ := hmode
      refine ⟨h1, ?_, ?_⟩
      · rw [hpc1, partCnt_of_rel L pd hR]; exact h2
      · rw [hpc1, hR.2.2.2.1]; exact h3
  obtain ⟨C, p2, T, hCv, hT0, hTc, hbC, hCx, KK2, hkT, hpc2, hi2⟩ :=
    ins_any L pd h4 B1 l S hv hvk y m hok
  -- lanes
  have hlane : ∀ l' r, r < llen L s l' →
      (C (lcell s l' r)).val ≠ 0 ∧
        classOf pd.hd (C (lcell s l' r)) = (ρ.step s (.hop l J y m)).lane l' r := by
    intro l' r hr
    rw [step_hop_lane]
    have hrk := rkey_lcell L pd l' hr
    by_cases hv' : lcell (n := n) s l' r = blank B1
    · rw [hb1] at hv'
      obtain ⟨rfl, rfl⟩ := lcell_inj L pd hr hPl hv'
      rw [hv', ← hb1, hCv, Function.update_self, shiftIn_self']
      exact ⟨hT0, hTc⟩
    · rw [hCx _ hv' (fun p' e => by rw [hrk] at e; cases e)]
      by_cases hl' : l' = l
      · subst hl'
        rw [Function.update_self]
        rcases Nat.lt_or_ge r P with hlt | hge
        · rw [hlane1 r hlt, shiftIn_of_lt hlt]
          exact prel_lane L pd hR l' (by omega)
        · have hgt : P < r := by
            rcases Nat.eq_or_lt_of_le hge with e | e
            · exact absurd (by rw [← e, hb1]) hv'
            · exact e
          rw [shiftIn_of_gt hgt, hB1x _ (fun hb => by
              have := rkey_inBoxOf L pd hb; rw [hrk] at this; cases this)
            (fun e => by have := hdk; rw [← e, hrk] at this; cases this)
            (fun r' hr' e => by have := (lcell_inj L pd hr (by omega) e).2; omega)]
          exact prel_lane L pd hR l' hr
      · rw [Function.update_of_ne hl', hB1x _ (fun hb => by
            have := rkey_inBoxOf L pd hb; rw [hrk] at this; cases this)
          (fun e => by have := hdk; rw [← e, hrk] at this; cases this)
          (fun r' hr' e => hl' (lcell_inj L pd hr (by omega) e).1)]
        exact prel_lane L pd hR l' hr
  -- region counts
  have hTB : T = B (position B1 T) := by
    have hk := hkT
    have hx : position B1 T = position B1 T := rfl
    obtain ⟨p', hp'⟩ : ∃ p' : Part, rkey L s σ pd.hd (position B1 T) = some (S, p') := by
      have := rkey_fst (σ := σ) L pd.hd (position B1 T)
      rw [hk] at this
      rcases e : rkey L s σ pd.hd (position B1 T) with _ | ⟨Q', p'⟩
      · rw [e] at this; cases this
      · rw [e] at this; simp only [Option.map_some, Option.some.injEq] at this
        exact ⟨p', by rw [this]⟩
    rw [← hB1S _ p' hp']; simp [position]
  have hposT : position B T = position B1 T := by
    conv_lhs => rw [hTB]
    simp [position]
  have hheadT : head ≠ T := by
    intro e
    have h1 : key L pd.hd (position B head) = none := by
      rw [show position B head = lcell s l 0 by simp [hhead, position]]
      rw [← rkey_fst (σ := σ) L pd.hd, rkey_lcell L pd l h0l]; rfl
    rw [e, hposT, hkT] at h1
    cases h1
  have hpC_head : position C head = d := by
    apply position_eq_of_apply
    rw [hCx d (fun e => by rw [e, hvk] at hdk; cases hdk)
      (fun p' e => by rw [hdk] at e; simp only [Option.some.injEq, Prod.mk.injEq] at e
                      exact hSD e.1.symm), hB1d]
  have hpC_T : position C T = blank B1 := position_eq_of_apply hCv
  have hcnt : ∀ Q y', regionCount L pd.hd C Q y' = (ρ.step s (.hop l J y m)).cnt Q y' := by
    intro Q y'
    have K := (keepKey_of_keepK L pd.hd K1).trans KK2
    rw [← Finset.insert_eq] at K
    have k1B : key L pd.hd (position B head) = none := by
      rw [show position B head = lcell s l 0 by simp [hhead, position]]
      rw [← rkey_fst (σ := σ) L pd.hd, rkey_lcell L pd l h0l]; rfl
    have k1C : key L pd.hd (position C head) = some D := by
      rw [hpC_head]; exact key_of_rkey L pd.hd hdk
    have k2B : key L pd.hd (position B T) = some S := by rw [hposT]; exact hkT
    have k2C : key L pd.hd (position C T) = none := by
      rw [hpC_T, ← rkey_fst (σ := σ) L pd.hd, hvk]; rfl
    rw [regionCount_move2 L pd.hd K hheadT hhead0 hT0 hSD k1B k1C k2B k2C Q y', hTc, hheadc]
    have hc : regionCount L pd.hd B = ρ.cnt := funext fun Q => funext fun y => hR.2.2.1 Q y
    rw [hc]
    rfl
  -- port counts
  have hpcB1 : pcOf L pd B1 = incP (pcOf L pd B) D pt (classOf pd.hd head) := by
    apply pc_landing L pd K1 hhead0
    · rw [show position B head = lcell s l 0 by simp [hhead, position]]
      exact rkey_lcell L pd l h0l
    · have : position B1 head = d := position_eq_of_apply hB1d
      rw [this, hdk]
  have hpcB : pcOf L pd B = ρ.pc := funext fun Q => funext fun pt => funext fun z => hR.2.2.2.1 Q pt z
  refine ⟨C, p1.append p2, prel_of_lanes L pd hlane hcnt ?_ ?_, ?_⟩
  · intro Q pt' z'
    show pcOf L pd C Q pt' z' = _
    rw [hpc2, hpcB1, hpcB, hheadc]
    rfl
  · show InBoxOf s σ S pt (blank C)
    exact hbC
  · rw [Path.inefficientMoves_append]
    have hj : ((Finset.range (P + 1)).filter fun r =>
        ¬ lgood l (classOf pd.hd (B (lcell s l r)))) =
        ((Finset.range (P + 1)).filter fun r => ¬ lgood l (ρ.lane l r)) := by
      apply Finset.filter_congr
      intro r hr
      rw [Finset.mem_range] at hr
      rw [(prel_lane L pd hR l (by omega)).2]
    rw [hj] at hi1
    have hk2 := pd.hd.two_le
    have hqk := pd.td.q_le
    cases m with
    | cheap =>
      show _ ≤ hopKc k σ + crossK q l J + ρ.ljunk l P + 0
      unfold PState.ljunk
      unfold insK insKc at hi2
      unfold hopKc crossK
      nlinarith
    | imp p z =>
      show _ ≤ hopKc k σ + crossK q l J + ρ.ljunk l P + hopKi k s σ
      unfold PState.ljunk
      unfold insK insKc insKi at hi2
      unfold hopKc hopKi crossK
      nlinarith

end SlidingPuzzle.Port
