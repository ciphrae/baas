import SlidingPuzzle.Port.Basic

/-! # Port primitives on boards

The relation `PRel` between a board and a `PState`, the boxes in absolute
coordinates, walks of the blank inside a box, and the refined keys of the cells
the operations touch. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext
  div_eq_iff_bounds)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} (L : LaneSys k q)

/-! ## Boxes -/

/-- Top row of a port's box, in local coordinates. -/
def boxR (k s σ : ℕ) : Pt → ℕ
  | .tl => k + 1
  | .tr => k + 1
  | .bl => s - 1 - σ

/-- Left column of a port's box, in local coordinates. -/
def boxC (k s σ : ℕ) : Pt → ℕ
  | .tl => k + 1
  | .tr => s - 1 - σ
  | .bl => k + 1

theorem inBox_iff (hσ : σ + 1 ≤ s) (pt : Pt) (r c : ℕ) :
    inBox k s σ pt r c ↔
      boxR k s σ pt ≤ r ∧ r < boxR k s σ pt + σ ∧ boxC k s σ pt ≤ c ∧ c < boxC k s σ pt + σ := by
  cases pt <;> simp only [inBox, boxR, boxC] <;> omega

theorem box_bounds (pd : PDims n k s q σ) (pt : Pt) :
    k + 1 ≤ boxR k s σ pt ∧ boxR k s σ pt + σ + 1 ≤ s ∧
      k + 1 ≤ boxC k s σ pt ∧ boxC k s σ pt + σ + 1 ≤ s := by
  have hf := pd.fit
  cases pt <;> simp only [boxR, boxC] <;> omega

/-- The blank's cell lies in the box of port `pt` of `Q`. -/
def InBoxOf (s σ : ℕ) (Q : Sq k) (pt : Pt) (x : Cell n) : Prop :=
  x.1.val / s = Q.1.val ∧ x.2.val / s = Q.2.val ∧ inBox k s σ pt (x.1.val % s) (x.2.val % s)

section cells
variable [NeZero n]

theorem inBoxOf_lc (pd : PDims n k s q σ) (Q : Sq k) {pt : Pt} {r c : ℕ} (h : inBox k s σ pt r c) :
    InBoxOf s σ Q pt (lc (n := n) s Q r c) := by
  have hb := box_bounds pd pt
  have hσ : σ + 1 ≤ s := by have := pd.fit; omega
  rw [inBox_iff hσ] at h
  obtain ⟨d1, d2, d3, d4⟩ := lc_div (n := n) pd.hd Q (r := r) (c := c) (by omega) (by omega)
  refine ⟨d1, d3, ?_⟩
  rw [d2, d4, inBox_iff hσ]; exact h

theorem inBoxOf_iff (pd : PDims n k s q σ) {Q : Sq k} {pt : Pt} {x : Cell n} :
    InBoxOf s σ Q pt x ↔ ∃ r c, inBox k s σ pt r c ∧ x = lc s Q r c := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨_, _, h3, ?_⟩
    have := eq_lc pd.hd x
    have hq : sqOf pd.hd x = Q := Prod.ext (Fin.ext h1) (Fin.ext h2)
    rw [hq] at this; exact this
  · rintro ⟨r, c, h, rfl⟩; exact inBoxOf_lc pd Q h

theorem rkey_inBoxOf (pd : PDims n k s q σ) {Q : Sq k} {pt : Pt} {x : Cell n}
    (h : InBoxOf s σ Q pt x) : rkey L s σ pd.hd x = some (Q, some pt) := by
  obtain ⟨r, c, hb, rfl⟩ := (inBoxOf_iff pd).1 h
  exact rkey_box L pd Q hb

/-- Walk the blank inside a port box: only box cells change, so every refined key is kept. -/
theorem exists_box_walk (pd : PDims n k s q σ) (h3 : 3 ≤ σ) (B : Board n) {Q : Sq k} {pt : Pt}
    (hb : InBoxOf s σ Q pt (blank B)) {e : Cell n} (he : InBoxOf s σ Q pt e) :
    ∃ C : Board n, ∃ p : Path B C, blank C = e ∧ p.inefficientMoves ≤ 2 * σ ∧
      (∀ x, ¬ InBoxOf s σ Q pt x → C x = B x) ∧ KeepK (rkey L s σ pd.hd) B C ∅ := by
  have hbd := box_bounds pd pt
  have hb1 := pd.hd.band_le Q.1.isLt
  have hb2 := pd.hd.band_le Q.2.isLt
  have hs := pd.hd.s_pos
  have key : ∀ x : Cell n, InBoxOf s σ Q pt x ↔
      (Q.1.val * s + boxR k s σ pt ≤ x.1.val ∧ x.1.val ≤ Q.1.val * s + (boxR k s σ pt + σ - 1) ∧
        Q.2.val * s + boxC k s σ pt ≤ x.2.val ∧ x.2.val ≤ Q.2.val * s + (boxC k s σ pt + σ - 1)) := by
    intro x
    unfold InBoxOf
    rw [inBox_iff (by have := pd.fit; omega)]
    have e1 := Nat.div_add_mod x.1.val s
    have e2 := Nat.div_add_mod x.2.val s
    have m1 := Nat.mod_lt x.1.val hs
    have m2 := Nat.mod_lt x.2.val hs
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      rw [h1] at e1; rw [h2] at e2
      rw [mul_comm] at e1 e2
      omega
    · rintro ⟨h1, h2, h3, h4⟩
      have d1 : x.1.val / s = Q.1.val := by
        rw [div_eq_iff_bounds hs]; omega
      have d2 : x.2.val / s = Q.2.val := by
        rw [div_eq_iff_bounds hs]; omega
      rw [d1] at e1; rw [d2] at e2
      rw [mul_comm] at e1 e2
      refine ⟨d1, d2, ?_, ?_, ?_, ?_⟩ <;> omega
  rw [key] at hb he
  obtain ⟨C, p, hbC, hl, hr, -⟩ := SlidingPuzzle.exists_rect_walk_avoid B
    (Q.1.val * s + boxR k s σ pt) (Q.1.val * s + (boxR k s σ pt + σ - 1))
    (Q.2.val * s + boxC k s σ pt) (Q.2.val * s + (boxC k s σ pt + σ - 1))
    (by omega) (by omega) (by omega) e hb he
  refine ⟨C, p, hbC, by have := p.inefficientMoves_le_length; omega,
    fun x hx => hr x (fun h => hx ((key x).2 h)), ?_⟩
  exact keepK_of_agree (rkey L s σ pd.hd) (fun x => InBoxOf s σ Q pt x)
    (fun x y hx hy => by rw [rkey_inBoxOf L pd hx, rkey_inBoxOf L pd hy])
    (fun x hx => hr x (fun h => hx ((key x).2 h)))

/-- Lane cells have no refined key. -/
theorem rkey_rowCell (pd : PDims n k s q σ) (H : LaneI k q) (p : ℕ) (hp : p < rowLen L s H) :
    rkey L s σ pd.hd (rowCell (n := n) s H p) = none :=
  rkey_of_key_none L pd.hd (key_rowCell L pd.td H p hp)

theorem rkey_colCell (pd : PDims n k s q σ) (V : LaneI k q) (p : ℕ) (hp : p < colLen L s V) :
    rkey L s σ pd.hd (colCell (n := n) s V p) = none :=
  rkey_of_key_none L pd.hd (key_colCell L pd.td V p hp)

end cells

/-! ## The relation -/

variable [NeZero n]

/-- A board realizes a `PState`. -/
def PRel (pd : PDims n k s q σ) (B : Board n) (ρ : PState k q) : Prop :=
  (∀ H p, p < rowLen L s H →
    (B (rowCell s H p)).val ≠ 0 ∧ classOf pd.hd (B (rowCell s H p)) = ρ.row H p) ∧
  (∀ V p, p < colLen L s V →
    (B (colCell s V p)).val ≠ 0 ∧ classOf pd.hd (B (colCell s V p)) = ρ.col V p) ∧
  (∀ Q y, regionCount L pd.hd B Q y = ρ.cnt Q y) ∧
  (∀ Q pt y, pcount L s σ pd.hd B Q (some pt) y = ρ.pc Q pt y) ∧
  InBoxOf s σ ρ.blank ρ.bp (blank B)

/-- The main count is the region count minus the port counts. -/
theorem pcount_main (pd : PDims n k s q σ) (B : Board n) (Q y : Sq k) :
    pcount L s σ pd.hd B Q none y + ∑ pt, pcount L s σ pd.hd B Q (some pt) y =
      regionCount L pd.hd B Q y := by
  rw [regionCount_eq_sum L (σ := σ), Fintype.sum_option]

theorem mcnt_of_rel (pd : PDims n k s q σ) {B : Board n} {ρ : PState k q} (hR : PRel L pd B ρ)
    (Q y : Sq k) : pcount L s σ pd.hd B Q none y = ρ.mcnt Q y := by
  have h := pcount_main L pd B Q y
  rw [hR.2.2.1 Q y] at h
  simp only [hR.2.2.2.1] at h
  unfold PState.mcnt
  omega

theorem partCnt_of_rel (pd : PDims n k s q σ) {B : Board n} {ρ : PState k q} (hR : PRel L pd B ρ)
    (Q : Sq k) (p : Part) (y : Sq k) : pcount L s σ pd.hd B Q p y = ρ.partCnt Q p y := by
  cases p with
  | none => exact mcnt_of_rel L pd hR Q y
  | some pt => exact hR.2.2.2.1 Q pt y

end SlidingPuzzle.Port
