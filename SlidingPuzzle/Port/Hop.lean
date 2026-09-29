import SlidingPuzzle.Port.InsOp

/-! # A hop realized on the board

Landing from the lane's port at the landing square (`landR`, `landC`), then insertion
at the source (`ins_cheap`, `ins_imp`); the resulting board realizes the stepped
`PState`. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext InBox
  div_eq_iff_bounds shiftIn shiftIn_of_lt shiftIn_self' shiftIn_of_gt incCnt decCnt
  apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-! ## Lanes of either axis -/

/-- Position `r` of a lane of either axis. -/
def lcell (s : ℕ) (l : Ln k q) (r : ℕ) : Cell n := if l.1 then colCell s l.2 r else rowCell s l.2 r

theorem rkey_lcell (pd : PDims n k s q σ) (l : Ln k q) {r : ℕ} (hr : r < llen L s l) :
    rkey L s σ pd.hd (lcell (n := n) s l r) = none := by
  unfold lcell llen at *
  split_ifs at hr ⊢
  · exact rkey_colCell L pd l.2 r hr
  · exact rkey_rowCell L pd l.2 r hr

theorem lcell_inj (pd : PDims n k s q σ) {l l' : Ln k q} {r r' : ℕ} (hr : r < llen L s l)
    (hr' : r' < llen L s l') (h : lcell (n := n) s l r = lcell s l' r') : l = l' ∧ r = r' := by
  obtain ⟨a, H⟩ := l
  obtain ⟨a', H'⟩ := l'
  unfold lcell llen at *
  cases a <;> cases a' <;> simp only [Bool.false_eq_true, if_false, if_true] at h hr hr'
  · obtain ⟨e1, e2⟩ := rowCell_inj L pd.td hr hr' h; subst e1; exact ⟨rfl, e2⟩
  · exact absurd h (rowCell_ne_colCell L pd.td H H' r r' hr')
  · exact absurd h.symm (rowCell_ne_colCell L pd.td H' H r' r hr)
  · obtain ⟨e1, e2⟩ := colCell_inj L pd.td hr hr' h; subst e1; exact ⟨rfl, e2⟩

theorem lposP_geom (pd : PDims n k s q σ) (l : Ln k q) (J : Fin k) (hJ : LIn L l.2 J) :
    lposP k s l J < llen L s l ∧
      lcell (n := n) s l (lposP k s l J) =
        lc s (src l J) (lineRC k s l l.2.o.val).1 (lineRC k s l l.2.o.val).2 := by
  have hq := l.2.o.isLt
  have hqk := pd.td.q_le
  have hks := pd.td.k_lt_s
  obtain ⟨a, H⟩ := l
  have hq' : H.o.val < q := H.o.isLt
  cases a
  · obtain ⟨h1, h2⟩ := rowPos_geom L pd.td H J hJ
    refine ⟨h1, ?_⟩
    simp only [lcell, lposP, llen, src, lineRC, Bool.false_eq_true, if_false] at h1 ⊢
    dsimp only at h1 h2 hq ⊢
    cases hs : H.side <;> simp only [hs, if_true, if_false, Bool.false_eq_true] at h2 ⊢ <;>
      apply cell_ext
    · rw [rowCell_fst pd.td, lc_fst (n := n) pd.hd (H.b, J) k (show H.o.val < s by omega)]
    · rw [rowCell_snd L pd.td H _ h1, h2, lc_snd (n := n) pd.hd (H.b, J) H.o.val
        (show k < s by omega)]
    · rw [rowCell_fst pd.td, lc_fst (n := n) pd.hd (H.b, J) (s - 1) (show H.o.val < s by omega)]
    · rw [rowCell_snd L pd.td H _ h1, h2, lc_snd (n := n) pd.hd (H.b, J) H.o.val
        (show s - 1 < s by omega)]
      dsimp only
      omega
  · obtain ⟨h1, h2, h3⟩ := colPosP_geom L pd.td H J hJ
    refine ⟨h1, ?_⟩
    simp only [lcell, lposP, llen, src, lineRC, if_true] at h1 h2 h3 ⊢
    dsimp only at h1 h2 h3 hq ⊢
    cases hs : H.side <;> simp only [hs, if_true, if_false, Bool.false_eq_true] at h3 ⊢ <;>
      apply cell_ext
    · rw [colCell_fst L pd.td H _ h1, h2, h3, lc_fst (n := n) pd.hd (J, H.b) H.o.val
        (show k < s by omega)]
    · rw [colCell_snd pd.td, lc_snd (n := n) pd.hd (J, H.b) k (show H.o.val < s by omega)]
    · rw [colCell_fst L pd.td H _ h1, h2, h3, lc_fst (n := n) pd.hd (J, H.b) H.o.val
        (show s - 1 < s by omega)]
    · rw [colCell_snd pd.td, lc_snd (n := n) pd.hd (J, H.b) (s - 1) (show H.o.val < s by omega)]

/-- The lane part of `PRel`, for lanes of either axis. -/
theorem prel_lane (pd : PDims n k s q σ) {B : Board n} {ρ : PState k q} (hR : PRel L pd B ρ)
    (l : Ln k q) {r : ℕ} (hr : r < llen L s l) :
    (B (lcell s l r)).val ≠ 0 ∧ classOf pd.hd (B (lcell s l r)) = ρ.lane l r := by
  unfold lcell PState.lane llen at *
  split_ifs at hr ⊢
  · exact hR.2.1 l.2 r hr
  · exact hR.1 l.2 r hr

/-- A landing on either axis. -/
theorem land_any (pd : PDims n k s q σ) (h3 : 3 ≤ σ) (B : Board n) (l : Ln k q) (J : Fin k)
    (hJ : LIn L l.2 J) (hbl : InBoxOf s σ (land l) (lport l) (blank B)) :
    ∃ C : Board n, ∃ p : Path B C, blank C = lcell s l (lposP k s l J) ∧
      (∀ r, r < lposP k s l J → C (lcell s l r) = B (lcell s l (r + 1))) ∧
      (∃ d : Cell n, rkey L s σ pd.hd d = some (land l, some (lport l)) ∧
        C d = B (lcell s l 0) ∧
        (∀ x, ¬ InBoxOf s σ (land l) (lport l) x → x ≠ d →
          (∀ r, r ≤ lposP k s l J → x ≠ lcell s l r) → C x = B x)) ∧
      KeepK (rkey L s σ pd.hd) B C {B (lcell s l 0)} ∧
      p.inefficientMoves ≤ 2 * σ + 14 * k + 35 + 7 * (q + 2) * LaneSys.pdist l.2.t.val J.val +
        ((Finset.range (lposP k s l J + 1)).filter fun r =>
          ¬ lgood l (classOf pd.hd (B (lcell s l r)))).card := by
  obtain ⟨a, H⟩ := l
  cases a
  · obtain ⟨C, p, h1, h2, h3', h4, h5, h6⟩ := landR L pd h3 B hJ hbl
    have hpos := blen_pos_of_in L hJ
    refine ⟨C, p, h1, h2, ⟨dropR s H, rkey_dropR L pd H hpos, h3', h4⟩, h5, ?_⟩
    simp only [lcell, lposP, lgood, Bool.false_eq_true, if_false] at h6 ⊢
    have : 0 ≤ 7 * (q + 2) * LaneSys.pdist H.t.val J.val := Nat.zero_le _
    omega
  · obtain ⟨C, p, h1, h2, h3', h4, h5, h6⟩ := landC L pd h3 B hJ hbl
    have hpos := blen_pos_of_in L hJ
    refine ⟨C, p, h1, h2, ⟨dropC k s H, rkey_dropC L pd H hpos, h3', h4⟩, h5, ?_⟩
    simp only [lcell, lposP, lgood, if_true] at h6 ⊢
    exact h6

/-! ## Keys -/

theorem keepKey_of_keepK (hd : HDims n k s) {B C : Board n} {M : Finset (Tile n)}
    (h : KeepK (rkey L s σ hd) B C M) : KeepKey L hd B C M := by
  intro t ht htM
  rw [← rkey_fst (σ := σ) L hd, ← rkey_fst (σ := σ) L hd, h t ht htM]

theorem src_ne_land {l : Ln k q} {J : Fin k} (hJ : LIn L l.2 J) : src l J ≠ land l := by
  have hne := LaneSys.inPiece_lt hJ
  obtain ⟨a, H⟩ := l
  dsimp only at hne
  cases a <;> simp only [src, land, rowLand, colLand, Bool.false_eq_true, if_false, if_true] <;>
    intro e
  · have := congrArg Prod.snd e
    simp only at this
    rcases hne with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [this] at h' <;> omega
  · have := congrArg Prod.fst e
    simp only at this
    rcases hne with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [this] at h' <;> omega

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

/-- Budget of the insertion of a hop. -/
def insK (k q s σ : ℕ) : Mode k → ℕ
  | .cheap => insKc k q σ
  | .imp _ _ => insKc k q σ + insKi k q s σ

/-- Port counts of a board. -/
noncomputable def pcOf (pd : PDims n k s q σ) (B : Board n) : Sq k → Pt → Sq k → ℕ :=
  fun Q pt z => pcount L s σ pd.hd B Q (some pt) z

/-- The insertion can be carried out on the board. -/
def InsOK (pd : PDims n k s q σ) (B : Board n) (S : Sq k) (pt : Pt) (y : Sq k) : Mode k → Prop
  | .cheap => 1 ≤ pcount L s σ pd.hd B S (some pt) y
  | .imp p z => p ≠ some pt ∧ 1 ≤ pcount L s σ pd.hd B S p y ∧
      1 ≤ pcount L s σ pd.hd B S (some pt) z

/-- An insertion in either mode, with its effect on counts. -/
theorem ins_any (pd : PDims n k s q σ) (h4 : 4 ≤ σ) (B : Board n) (l : Ln k q) (S : Sq k)
    (hv : blank B = lc s S (lineRC k s l l.2.o.val).1 (lineRC k s l l.2.o.val).2)
    (hvk : rkey L s σ pd.hd (blank B) = none) (y : Sq k) (m : Mode k)
    (hok : InsOK L pd B S (lport l) y m) :
    ∃ C : Board n, ∃ p : Path B C, ∃ T : Tile n,
      C (blank B) = T ∧ T.val ≠ 0 ∧ classOf pd.hd T = y ∧
      InBoxOf s σ S (lport l) (blank C) ∧
      (∀ x, x ≠ blank B → (∀ p : Part, rkey L s σ pd.hd x ≠ some (S, p)) → C x = B x) ∧
      KeepKey L pd.hd B C {T} ∧ key L pd.hd (position B T) = some S ∧
      (∀ Q pt z, pcOf L pd C Q pt z = PState.srcPc (pcOf L pd B) S (lport l) y m Q pt z) ∧
      p.inefficientMoves ≤ insK k q s σ m := by
  have ho : l.2.o.val < q := l.2.o.isLt
  set pt := lport l with hpt
  cases m with
  | cheap =>
    obtain ⟨t, htk, ht0, htc⟩ := exists_of_kcount (rkey L s σ pd.hd) pd.hd B (by exact hok)
    obtain ⟨C, p, hCv, hbC, hCx, K, hi⟩ := ins_cheap L pd h4 B l S ho hv hvk htk
    have hpB : position B (B t) = t := by simp [position]
    have hpC : position C (B t) = blank B := position_eq_of_apply hCv
    refine ⟨C, p, B t, hCv, ht0, htc, hbC, fun x hxv hx => hCx x hxv (hx _),
      keepKey_of_keepK L pd.hd K, by rw [hpB]; exact key_of_rkey L pd.hd htk, ?_, hi⟩
    intro Q pt' z
    have e := kcount_move1 (rkey L s σ pd.hd) pd.hd K ht0 (some (Q, some pt')) z
    rw [hpB, hpC, htk, hvk, htc] at e
    unfold pcOf pcount PState.srcPc decP
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, if_false,
      add_zero] at e ⊢
    by_cases h : Q = S ∧ pt' = pt ∧ z = y
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [and_self, if_true] at e ⊢
      omega
    · rw [if_neg h]
      rw [if_neg (by rintro ⟨⟨h1, h2⟩, h3⟩; exact h ⟨h1.symm, h2.symm, h3.symm⟩)] at e
      omega
  | imp p z =>
    obtain ⟨hp, hy, hz⟩ := hok
    obtain ⟨ty, htyk, hty0, htyc⟩ := exists_of_kcount (rkey L s σ pd.hd) pd.hd B hy
    obtain ⟨tz, htzk, htz0, htzc⟩ := exists_of_kcount (rkey L s σ pd.hd) pd.hd B hz
    obtain ⟨C, p', hCv, hCty, hbC, hCx, K, hi⟩ := ins_imp L pd h4 B l S ho hv hvk hp htyk htzk
    have htyz : ty ≠ tz := ne_of_rkey L (by
      rw [htyk, htzk]; intro e; simp only [Option.some.injEq, Prod.mk.injEq, true_and] at e
      exact hp e)
    have hTZ : B ty ≠ B tz := fun e => htyz (B.injective e)
    have hpB1 : position B (B ty) = ty := by simp [position]
    have hpB2 : position B (B tz) = tz := by simp [position]
    have hpC1 : position C (B ty) = blank B := position_eq_of_apply hCv
    have hpC2 : position C (B tz) = ty := position_eq_of_apply hCty
    have KK : KeepKey L pd.hd B C {B ty} := by
      have K' := keepKey_of_keepK L pd.hd K
      intro t h0 ht
      by_cases e : t = B tz
      · subst e
        rw [hpC2, hpB2, key_of_rkey L pd.hd htyk, key_of_rkey L pd.hd htzk]
      · exact K' t h0 (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht ⊢
                          exact ⟨ht, e⟩)
    refine ⟨C, p', B ty, hCv, hty0, htyc, hbC,
      fun x hxv hx => hCx x hxv (fun e => hx p (by rw [e]; exact htyk)) (hx _), KK,
      by rw [hpB1]; exact key_of_rkey L pd.hd htyk, ?_, hi⟩
    intro Q pt' z'
    have e := kcount_move2 (rkey L s σ pd.hd) pd.hd K hTZ hty0 htz0 (some (Q, some pt')) z'
    rw [hpB1, hpB2, hpC1, hpC2, htyk, htzk, hvk, htyc, htzc] at e
    have hyp : 1 ≤ pcOf L pd B S pt z := hz
    -- everything as indicators of the triple `(Q, some pt', z')`
    set τ : Sq k × Part × Sq k := (Q, some pt', z') with hτ
    have r : ∀ (A : Sq k) (a : Part) (c : Sq k),
        (some (A, a) = some (Q, some pt') ∧ c = z') ↔ ((A, a, c) = τ) := by
      intro A a c; simp [hτ, Prod.ext_iff, and_assoc]
    have r0 : ∀ c : Sq k, ((none : Option (Sq k × Part)) = some (Q, some pt') ∧ c = z') ↔ False := by
      intro c; simp
    have g : ∀ (A : Sq k) (a : Pt) (c : Sq k),
        (Q = A ∧ pt' = a ∧ z' = c) ↔ (τ = (A, some a, c)) := by
      intro A a c; simp [hτ, Prod.ext_iff]
    simp only [r, r0, if_false, add_zero, zero_add] at e
    unfold pcOf pcount at hyp ⊢
    cases p with
    | none =>
      simp only [PState.srcPc]
      unfold decP
      simp only [g]
      have hn : ((S, (none : Part), y) = τ) ↔ False := by simp [hτ, Prod.ext_iff]
      have hn' : ((S, (none : Part), z) = τ) ↔ False := by simp [hτ, Prod.ext_iff]
      simp only [hn, hn', if_false, add_zero, zero_add] at e
      by_cases h : τ = (S, some pt, z)
      · rw [if_pos h, if_pos h.symm] at *
        omega
      · rw [if_neg h, if_neg (fun h' => h h'.symm)] at *
        omega
    | some p' =>
      have hp' : p' ≠ pt := fun e => hp (by rw [e])
      have hyp' : 1 ≤ kcount (rkey L s σ pd.hd) pd.hd B (some (S, some p')) y := hy
      simp only [PState.srcPc]
      unfold decP incP
      simp only [g]
      have hab : ((S, (some p' : Part), y) : Sq k × Part × Sq k) ≠ (S, some pt, z) := by
        simp [Prod.ext_iff, hp']
      have hbc : ((S, (some pt : Part), z) : Sq k × Part × Sq k) ≠ (S, some p', z) := by
        simp [Prod.ext_iff, Ne.symm hp']
      have e1 : ∀ x : Sq k × Part × Sq k, (if x = τ then 1 else 0) = (if τ = x then 1 else 0) :=
        fun x => by by_cases h : x = τ <;> simp [h, eq_comm]
      simp only [e1] at e
      by_cases ha : τ = (S, some p', y)
      · have hb : ¬ τ = (S, some pt, z) := fun hb => hab (ha.symm.trans hb)
        have h' := hτ ▸ ha
        simp only [Prod.mk.injEq, Option.some.injEq] at h'
        obtain ⟨hQ, hpt', hz'⟩ := h'
        by_cases hc : τ = (S, some p', z)
        · simp only [ha, hb, hc, if_true, if_false] at e ⊢
          rw [hQ, hpt', hz'] at e ⊢
          omega
        · simp only [ha, hb, hc, if_true, if_false] at e ⊢
          rw [hQ, hpt', hz'] at e ⊢
          omega
      · have hab' : ¬ (((S, (some pt : Part), z) : Sq k × Part × Sq k) = (S, some p', y)) :=
          fun h => hab h.symm
        by_cases hb : τ = (S, some pt, z) <;> by_cases hc : τ = (S, some p', z)
        · exact absurd (hb.symm.trans hc) hbc
        · simp only [ha, hb, hc, hab', hbc, if_true, if_false] at e ⊢; omega
        · have h1 : ¬ (((S, (some p' : Part), z) : Sq k × Part × Sq k) = (S, some p', y)) :=
            fun h => ha (hc.trans h)
          have h2 : ¬ (((S, (some p' : Part), z) : Sq k × Part × Sq k) = (S, some pt, z)) :=
            fun h => hbc h.symm
          simp only [ha, hb, hc, h1, h2, if_true, if_false] at e ⊢; omega
        · simp only [ha, hb, hc, if_true, if_false] at e ⊢; omega

end SlidingPuzzle.Port
