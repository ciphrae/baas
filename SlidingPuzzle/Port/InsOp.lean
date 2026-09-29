import SlidingPuzzle.Port.Ins

/-! # Insertion on boards: cheap and importing -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext InBox
  div_eq_iff_bounds exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist
  reflC apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- Budget of a cheap insertion. -/
def insKc (k q σ : ℕ) : ℕ := 10 * σ + 430 * k + 82 * q + 1500

/-- Extra budget of an importing insertion. -/
def insKi (k q s σ : ℕ) : ℕ := 10 * s + 10 * σ + 800 * k + 82 * q + 2500

theorem cr0_eq (pt : Pt) : cr0 k s σ pt = if cfr pt then s - (k + 2 + σ) else 0 := by
  cases pt <;> rfl

theorem cc0_eq (pt : Pt) : cc0 k s σ pt = if cfc pt then s - (k + 2 + σ) else 0 := by
  cases pt <;> rfl

theorem rest_lt (pd : PDims n k s q σ) (l : Ln k q) (o : ℕ) :
    (restRC k s l o).1 < s ∧ (restRC k s l o).2 < s := by
  have hf := pd.fit
  have h2 : (k + o + 1) % 2 ≤ 1 := by omega
  unfold restRC; split_ifs <;> simp <;> omega

theorem line_lt (pd : PDims n k s q σ) (l : Ln k q) {o : ℕ} (ho : o < q) :
    (lineRC k s l o).1 < s ∧ (lineRC k s l o).2 < s := by
  have hf := pd.fit
  have hqk := pd.td.q_le
  unfold lineRC; split_ifs <;> simp <;> omega

theorem spare_lt (pd : PDims n k s q σ) (pt : Pt) (i : Fin 3) :
    (spare k s pt i).1 < s ∧ (spare k s pt i).2 < s := by
  have hf := pd.fit
  have := i.isLt
  cases pt <;> simp only [spare] <;> split_ifs <;> omega

/-- The jump from a line cell to the rest cell next to it. -/
theorem jump_line_rest (pd : PDims n k s q σ) (l : Ln k q) (Q : Sq k) {o : ℕ} (ho : o < q)
    (B' : Board n) (hB' : blank B' = lc s Q (lineRC k s l o).1 (lineRC k s l o).2) :
    ∃ p : Path B' (swapCells B' (blank B') (lc s Q (restRC k s l o).1 (restRC k s l o).2)),
      p.inefficientMoves ≤ 7 * (k + 3) := by
  have hf := pd.fit
  have hqk := pd.td.q_le
  obtain ⟨hl1, hl2⟩ := line_lt pd l ho
  obtain ⟨hr1, hr2⟩ := rest_lt pd l o
  set v : Cell n := lc s Q (lineRC k s l o).1 (lineRC k s l o).2 with hv
  set w : Cell n := lc s Q (restRC k s l o).1 (restRC k s l o).2 with hw
  have a1 : v.1.val = Q.1.val * s + (lineRC k s l o).1 := lc_fst pd.hd Q _ hl1
  have a2 : v.2.val = Q.2.val * s + (lineRC k s l o).2 := lc_snd pd.hd Q _ hl2
  have b1 : w.1.val = Q.1.val * s + (restRC k s l o).1 := lc_fst pd.hd Q _ hr1
  have b2 : w.2.val = Q.2.val * s + (restRC k s l o).2 := lc_snd pd.hd Q _ hr2
  generalize Q.1.val * s = R at *
  generalize Q.2.val * s = C at *
  have h2 : (k + o + 1) % 2 ≤ 1 := by omega
  rcases lport_cases l with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ <;>
    simp only [lineRC, restRC, e1, e2, if_true, if_false, Bool.false_eq_true] at a1 a2 b1 b2
  · obtain ⟨p, hp⟩ := exists_hjump_step pd.hd.two_le_n B' w
      (by rw [hB', a1, b1]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    exact ⟨p, hp.trans (by rw [hB', a2, b2]; simp only [Nat.dist]; omega)⟩
  · obtain ⟨p, hp⟩ := exists_hjump_step pd.hd.two_le_n B' w
      (by rw [hB', a1, b1]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    exact ⟨p, hp.trans (by rw [hB', a2, b2]; simp only [Nat.dist]; omega)⟩
  · obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' w
      (by rw [hB', a2, b2]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    exact ⟨p, hp.trans (by rw [hB', a1, b1]; simp only [Nat.dist]; omega)⟩
  · obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' w
      (by rw [hB', a2, b2]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    exact ⟨p, hp.trans (by rw [hB', a1, b1]; simp only [Nat.dist]; omega)⟩

/-- Cells of a port lie in its corner box. -/
theorem inCorner_of_rkey (pd : PDims n k s q σ) {Q : Sq k} {pt : Pt} {x : Cell n}
    (h : rkey L s σ pd.hd x = some (Q, some pt)) :
    InBox (Q.1.val * s + cr0 k s σ pt) (Q.2.val * s + cc0 k s σ pt) (k + 2 + σ) x := by
  have hs := pd.hd.s_pos
  obtain ⟨hreg, hp⟩ := (rkey_eq_some L pd.hd).1 h
  have hloc := (partOf_eq_some pd (Nat.mod_lt _ hs) (Nat.mod_lt _ hs)).1 hp
  have hc := portLoc_corner pd.fit pd.td.q_le (Nat.mod_lt _ hs) (Nat.mod_lt _ hs) hloc
  have e1 := Nat.div_add_mod x.1.val s
  have e2 := Nat.div_add_mod x.2.val s
  rw [hreg.1] at e1; rw [hreg.2.1] at e2
  rw [mul_comm] at e1 e2
  unfold InBox; omega

theorem inCorner_lc (pd : PDims n k s q σ) (Q : Sq k) (pt : Pt) {r c : ℕ}
    (h1 : cr0 k s σ pt ≤ r) (h2 : r < cr0 k s σ pt + (k + 2 + σ))
    (h3 : cc0 k s σ pt ≤ c) (h4 : c < cc0 k s σ pt + (k + 2 + σ)) (hr : r < s) (hc : c < s) :
    InBox (Q.1.val * s + cr0 k s σ pt) (Q.2.val * s + cc0 k s σ pt) (k + 2 + σ)
      (lc (n := n) s Q r c) := by
  unfold InBox; rw [lc_fst pd.hd Q _ hr, lc_snd pd.hd Q _ hc]; omega

theorem corner_fits (pd : PDims n k s q σ) (Q : Sq k) (pt : Pt) :
    Q.1.val * s + cr0 k s σ pt + (k + 2 + σ) ≤ n ∧ Q.2.val * s + cc0 k s σ pt + (k + 2 + σ) ≤ n := by
  have hf := pd.fit
  have h1 := pd.hd.band_le Q.1.isLt
  have h2 := pd.hd.band_le Q.2.isLt
  cases pt <;> simp only [cr0, cc0] <;> omega

theorem box_corner (pd : PDims n k s q σ) {pt : Pt} {r c : ℕ} (h : inBox k s σ pt r c) :
    cr0 k s σ pt ≤ r ∧ r < cr0 k s σ pt + (k + 2 + σ) ∧
      cc0 k s σ pt ≤ c ∧ c < cc0 k s σ pt + (k + 2 + σ) := by
  have hf := pd.fit
  have hb : r < s ∧ c < s := by cases pt <;> simp only [inBox] at h <;> omega
  exact portLoc_corner pd.fit pd.td.q_le hb.1 hb.2 (Or.inl h)

/-- A cheap insertion: a class tile of the port goes to the insertion cell. -/
theorem ins_cheap (pd : PDims n k s q σ) (h4 : 4 ≤ σ) (B : Board n) (l : Ln k q) (S : Sq k)
    {o : ℕ} (ho : o < q)
    (hv : blank B = lc s S (lineRC k s l o).1 (lineRC k s l o).2)
    (hvk : rkey L s σ pd.hd (blank B) = none)
    {t : Cell n} (ht : rkey L s σ pd.hd t = some (S, some (lport l))) :
    ∃ C : Board n, ∃ p : Path B C,
      C (blank B) = B t ∧ InBoxOf s σ S (lport l) (blank C) ∧
      (∀ x, x ≠ blank B → rkey L s σ pd.hd x ≠ some (S, some (lport l)) → C x = B x) ∧
      KeepK (rkey L s σ pd.hd) B C {B t} ∧
      p.inefficientMoves ≤ insKc k q σ := by
  have hf := pd.fit
  have hqk := pd.td.q_le
  set pt := lport l with hpt
  set v := blank B with hvdef
  set w : Cell n := lc s S (restRC k s l o).1 (restRC k s l o).2 with hw
  have hwbox : inBox k s σ pt (restRC k s l o).1 (restRC k s l o).2 :=
    rest_box (by omega) hf l o
  have hwk : rkey L s σ pd.hd w = some (S, some pt) := rkey_box L pd S hwbox
  have hvw : v ≠ w := ne_of_rkey L (by rw [hvk, hwk]; simp)
  have hvt : v ≠ t := ne_of_rkey L (by rw [hvk, ht]; simp)
  set B4 := swapCells B v w with hB4
  obtain ⟨pj, hpj⟩ : ∃ p : Path B B4, p.inefficientMoves ≤ 7 * (k + 3) :=
    jump_line_rest pd l S ho B hv
  have hB4v : B4 v = B w := by rw [hB4, hvdef, swapCells_at_left]
  have hB4w : B4 w = 0 := by rw [hB4, swapCells_at_right, hvdef, apply_blank]
  have hB4x : ∀ x, x ≠ v → x ≠ w → B4 x = B x := fun x h1 h2 =>
    swapCells_preserves B h1 h2
  have hbl4 : blank B4 = w := blank_eq_of_apply hB4w
  have hW0 : (B w).val ≠ 0 := val_ne_zero_of_ne_blank hvw.symm
  have K1 : KeepK (rkey L s σ pd.hd) B B4 {0, B w} := by
    have := keepK_of_agree_outside (rkey L s σ pd.hd) (B := B) (C := B4) {v, w}
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hB4x x hx.1 hx.2)
    rwa [Finset.image_insert, Finset.image_singleton, hvdef, apply_blank] at this
  have hbudget : 7 * (k + 3) ≤ insKc k q σ := by unfold insKc; omega
  by_cases htw : t = w
  · subst htw
    refine ⟨B4, pj, hB4v, by rw [hbl4]; exact inBoxOf_lc pd S hwbox, ?_, ?_, hpj.trans hbudget⟩
    · intro x h1 h2
      exact hB4x x h1 (fun e => h2 (by rw [e]; exact hwk))
    · intro t' h0 ht'
      apply K1 t' h0
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht' ⊢
      exact ⟨fun e => h0 (by rw [e]; rfl), ht'⟩
  -- a spare cell of the port, not `t`
  obtain ⟨i, hi, hut⟩ : ∃ i : Fin 3, i.val ≤ 1 ∧ lc (n := n) s S (spare k s pt i).1 (spare k s pt i).2 ≠ t := by
    by_cases h0 : lc (n := n) s S (spare k s pt 0).1 (spare k s pt 0).2 = t
    · refine ⟨1, by simp, fun h1 => ?_⟩
      have := spare_lt pd pt 0
      have := spare_lt pd pt 1
      have e := lc_inj pd.hd S (by omega) (by omega) (by omega) (by omega) (h0.trans h1.symm)
      have := spare_inj hf pt (Prod.ext e.1 e.2)
      exact absurd this (by decide)
    · exact ⟨0, by simp, h0⟩
  set u : Cell n := lc s S (spare k s pt i).1 (spare k s pt i).2 with hu
  have hubox := spare_box h4 hf pt i
  have huk : rkey L s σ pd.hd u = some (S, some pt) := rkey_box L pd S hubox
  have huw : u ≠ w := by
    have := spare_lt pd pt i
    have := rest_lt pd l o
    intro e
    have e' := lc_inj pd.hd S (by omega) (by omega) (by omega) (by omega) e
    exact spare_ne_rest hf l o i (Prod.ext e'.1 e'.2)
  have hvu : v ≠ u := ne_of_rkey L (by rw [hvk, huk]; simp)
  have hB4t : B4 t = B t := hB4x t (Ne.symm hvt) htw
  have hB4u : B4 u = B u := hB4x u (Ne.symm hvu) huw
  have hT0 : (B t).val ≠ 0 := val_ne_zero_of_ne_blank (Ne.symm hvt)
  have hU0 : (B u).val ≠ 0 := val_ne_zero_of_ne_blank (Ne.symm hvu)
  obtain ⟨hl1, hl2⟩ := line_lt pd l ho
  obtain ⟨hr1, hr2⟩ := rest_lt pd l o
  obtain ⟨hs1, hs2⟩ := spare_lt pd pt i
  obtain ⟨fit1, fit2⟩ := corner_fits pd S pt
  have lcorner := line_corner (σ := σ) hf hqk l ho
  obtain ⟨c1, c2, c3, c4⟩ := box_corner pd hwbox
  obtain ⟨u1, u2, u3, u4⟩ := box_corner pd hubox
  obtain ⟨C, p2, hp2, hCv, hCt, hCu, hCx⟩ := exists_box_three_cycle_near B4
    (S.1.val * s + cr0 k s σ pt) (S.2.val * s + cc0 k s σ pt) (k + 2 + σ) (cfr pt) (cfc pt)
    (by omega) fit1 fit2
    (by rw [hbl4]; exact inCorner_lc pd S pt c1 c2 c3 c4 hr1 hr2) v t u
    (by rw [hv]; exact inCorner_lc pd S pt lcorner.1 lcorner.2.1 lcorner.2.2.1 lcorner.2.2.2 hl1 hl2)
    (inCorner_of_rkey L pd ht) (inCorner_lc pd S pt u1 u2 u3 u4 hs1 hs2) hvt hvu (Ne.symm hut)
    (by rw [hB4v]; exact fun e => hW0 (by rw [e]; rfl))
    (by rw [hB4t]; exact fun e => hT0 (by rw [e]; rfl))
    (by rw [hB4u]; exact fun e => hU0 (by rw [e]; rfl))
  have hcd : cornerDist (S.1.val * s + cr0 k s σ pt) (S.2.val * s + cc0 k s σ pt) (k + 2 + σ)
      (cfr pt) (cfc pt) (blank B4) v u ≤ 5 * k + q + 12 := by
    rw [hbl4, hv, cr0_eq, cc0_eq]
    refine (cornerDist_le pd S pt (by omega) (by omega) hr1 hr2 hl1 hl2 hs1 hs2).trans ?_
    have h1 : cdist k s σ pt (restRC k s l o).1 (restRC k s l o).2 ≤ 2 * k + 3 :=
      cdist_rest (σ := σ) hf l o
    have h2 : cdist k s σ pt (lineRC k s l o).1 (lineRC k s l o).2 ≤ k + q :=
      cdist_line (σ := σ) hf hqk l ho
    have h3 := cdist_spare (σ := σ) hf pt i
    omega
  refine ⟨C, pj.append p2, by rw [hCv, hB4t], ?_, ?_, ?_, ?_⟩
  · rw [blank_eq_of_apply (show C w = 0 by rw [hCx w hvw.symm (fun e => htw e.symm) huw.symm, hB4w])]
    exact inBoxOf_lc pd S hwbox
  · intro x h1 h2
    have hxt : x ≠ t := fun e => h2 (by rw [e]; exact ht)
    have hxu : x ≠ u := fun e => h2 (by rw [e]; exact huk)
    have hxw : x ≠ w := fun e => h2 (by rw [e]; exact hwk)
    rw [hCx x h1 hxt hxu, hB4x x h1 hxw]
  · have K2 : KeepK (rkey L s σ pd.hd) B4 C {B w, B t, B u} := by
      have := keepK_of_agree_outside (rkey L s σ pd.hd) (B := B4) (C := C) {v, t, u}
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          exact hCx x hx.1 hx.2.1 hx.2.2)
      rwa [Finset.image_insert, Finset.image_insert, Finset.image_singleton, hB4v, hB4t,
        hB4u] at this
    have K := K1.trans K2
    intro t' h0 ht'
    rw [Finset.mem_singleton] at ht'
    by_cases e1 : t' = B w
    · subst e1
      have : position C (B w) = u := position_eq_of_apply (by rw [hCu, hB4v])
      rw [this, show position B (B w) = w by simp [position], huk, hwk]
    by_cases e2 : t' = B u
    · subst e2
      have : position C (B u) = t := position_eq_of_apply (by rw [hCt, hB4u])
      rw [this, show position B (B u) = u by simp [position], huk, ht]
    apply K t' h0
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨fun e => h0 (by rw [e]; rfl), e1⟩, e1, ht', e2⟩
  · rw [Path.inefficientMoves_append]
    unfold insKc
    have : 82 * cornerDist (S.1.val * s + cr0 k s σ pt) (S.2.val * s + cc0 k s σ pt) (k + 2 + σ)
      (cfr pt) (cfc pt) (blank B4) v u ≤ 82 * (5 * k + q + 12) := Nat.mul_le_mul_left _ hcd
    omega

end SlidingPuzzle.Port
