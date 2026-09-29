import SlidingPuzzle.Port.KeyCount

/-! # Ports: the layout

Every square has three *ports*, one per corner used by lane ends: `tl` (row lanes
before their landing block and column lanes before their landing band), `tr` (row
lanes after the landing block) and `bl` (column lanes after the landing band). In
square-local coordinates `(r, c)` a port is a box of side `σ` next to its *line*,
the cells where lane heads are dropped and gateway tiles inserted:

* `tl`: box `[k+1, k+1+σ)²`; line column `k` above row `q`, and row `k` left of column `q`;
* `tr`: box `[k+1, k+1+σ) × [s-1-σ, s-1)`; line column `s-1` above row `q`;
* `bl`: box `[s-1-σ, s-1) × [k+1, k+1+σ)`; line row `s-1` left of column `q`.

The *refined key* `rkey` of a cell is its region's square together with the port
the cell belongs to (`none` for the main part of the region). -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd div_eq_iff_bounds)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree (TDims LaneSys LaneCell region key key_eq_some key_eq_none regionCount
  region_sqOf)

/-- The three ports of a square. -/
inductive Pt where
  | tl
  | tr
  | bl
  deriving DecidableEq, Repr

instance : Fintype Pt := ⟨{.tl, .tr, .bl}, by intro x; cases x <;> simp⟩

/-- The part of a square's region: `none` is the main part. -/
abbrev Part := Option Pt

/-- Dimensions of the port layout. -/
structure PDims (n k s q σ : ℕ) : Prop where
  td : TDims n k s q
  two_le : 2 ≤ σ
  fit : 2 * σ + 2 * k + 8 ≤ s

variable {n k s q σ : ℕ}

theorem PDims.hd (pd : PDims n k s q σ) : HDims n k s := pd.td.hd

/-! ## Local predicates -/

/-- The box of a port, in local coordinates. -/
def inBox (k s σ : ℕ) : Pt → ℕ → ℕ → Prop
  | .tl, r, c => k + 1 ≤ r ∧ r < k + 1 + σ ∧ k + 1 ≤ c ∧ c < k + 1 + σ
  | .tr, r, c => k + 1 ≤ r ∧ r < k + 1 + σ ∧ s - 1 - σ ≤ c ∧ c < s - 1
  | .bl, r, c => s - 1 - σ ≤ r ∧ r < s - 1 ∧ k + 1 ≤ c ∧ c < k + 1 + σ

/-- The line of a port, in local coordinates. -/
def onLine (k s q : ℕ) : Pt → ℕ → ℕ → Prop
  | .tl, r, c => (r < q ∧ c = k) ∨ (r = k ∧ c < q)
  | .tr, r, c => r < q ∧ c = s - 1
  | .bl, r, c => r = s - 1 ∧ c < q

/-- The local cells of a port. -/
def PortLoc (k s q σ : ℕ) (pt : Pt) (r c : ℕ) : Prop := inBox k s σ pt r c ∨ onLine k s q pt r c

/-- The port containing a local position, if any. -/
noncomputable def partOf (k s q σ : ℕ) (r c : ℕ) : Part :=
  if PortLoc k s q σ .tl r c then some .tl
  else if PortLoc k s q σ .tr r c then some .tr
  else if PortLoc k s q σ .bl r c then some .bl
  else none

/-- Two ports never share a local cell. -/
theorem portLoc_unique (pd : PDims n k s q σ) {pt pt' : Pt} {r c : ℕ} (hr : r < s) (hc : c < s)
    (h : PortLoc k s q σ pt r c) (h' : PortLoc k s q σ pt' r c) : pt = pt' := by
  have hq := pd.td.q_le
  have hf := pd.fit
  have h2 := pd.two_le
  cases pt <;> cases pt' <;> first | rfl |
    (exfalso; simp only [PortLoc, inBox, onLine] at h h'; omega)

theorem partOf_eq_some (pd : PDims n k s q σ) {pt : Pt} {r c : ℕ} (hr : r < s) (hc : c < s) :
    partOf k s q σ r c = some pt ↔ PortLoc k s q σ pt r c := by
  unfold partOf
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 <;> cases h <;> assumption
  · intro h
    cases pt
    · rw [if_pos h]
    · rw [if_neg (fun h1 => by cases portLoc_unique pd hr hc h1 h), if_pos h]
    · rw [if_neg (fun h1 => by cases portLoc_unique pd hr hc h1 h),
        if_neg (fun h1 => by cases portLoc_unique pd hr hc h1 h), if_pos h]

theorem partOf_eq_none {r c : ℕ} :
    partOf k s q σ r c = none ↔ ∀ pt, ¬ PortLoc k s q σ pt r c := by
  unfold partOf
  constructor
  · intro h pt hp
    split_ifs at h with h1 h2 h3
    cases pt <;> contradiction
  · intro h
    rw [if_neg (h .tl), if_neg (h .tr), if_neg (h .bl)]

/-- Box positions are not lane positions. -/
theorem not_lane_of_box (pd : PDims n k s q σ) {pt : Pt} {r c : ℕ} (h : inBox k s σ pt r c) :
    q ≤ r ∧ q ≤ c := by
  have hq := pd.td.q_le
  have hf := pd.fit
  cases pt <;> simp only [inBox] at h <;> omega

/-! ## The refined key -/

variable (L : LaneSys k q)

/-- The square and part of the region containing a cell, if any. -/
noncomputable def rkey (s σ : ℕ) (hd : HDims n k s) (x : Cell n) : Option (Sq k × Part) :=
  if region L s (sqOf hd x) x then some (sqOf hd x, partOf k s q σ (x.1.val % s) (x.2.val % s))
  else none

theorem rkey_fst (hd : HDims n k s) (x : Cell n) :
    (rkey L s σ hd x).map Prod.fst = key L hd x := by
  unfold rkey SlidingPuzzle.Tree.key
  split_ifs <;> rfl

theorem rkey_eq_some (hd : HDims n k s) {x : Cell n} {Q : Sq k} {p : Part} :
    rkey L s σ hd x = some (Q, p) ↔
      region L s Q x ∧ partOf k s q σ (x.1.val % s) (x.2.val % s) = p := by
  unfold rkey
  constructor
  · intro h
    split_ifs at h with hr
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hr, rfl⟩
  · rintro ⟨hr, rfl⟩
    rw [region_sqOf L hd hr, if_pos hr]

theorem rkey_eq_none (hd : HDims n k s) {x : Cell n} :
    rkey L s σ hd x = none ↔ LaneCell L s x := by
  rw [← key_eq_none L hd, ← rkey_fst L hd x]
  cases rkey L s σ hd x <;> simp

theorem key_of_rkey (hd : HDims n k s) {x : Cell n} {Q : Sq k} {p : Part}
    (h : rkey L s σ hd x = some (Q, p)) : key L hd x = some Q := by
  rw [← rkey_fst L hd x, h]; rfl

theorem rkey_of_key_none (hd : HDims n k s) {x : Cell n} (h : key L hd x = none) :
    rkey L s σ hd x = none := by
  have := rkey_fst (σ := σ) L hd x
  rw [h] at this
  cases e : rkey L s σ hd x
  · rfl
  · rw [e] at this; cases this

theorem ne_of_rkey {hd : HDims n k s} {x y : Cell n}
    (h : rkey L s σ hd x ≠ rkey L s σ hd y) : x ≠ y := fun e => h (by rw [e])

/-! ## Local cells -/

/-- The cell at local position `(r, c)` of square `Q`. -/
def lc (s : ℕ) [NeZero n] (Q : Sq k) (r c : ℕ) : Cell n :=
  mkCell n (Q.1.val * s + r) (Q.2.val * s + c)

section local_cells
variable [NeZero n]

theorem lc_fst (hd : HDims n k s) (Q : Sq k) {r : ℕ} (c : ℕ) (hr : r < s) :
    (lc (n := n) s Q r c).1.val = Q.1.val * s + r :=
  mkCell_fst (by have := hd.band_le Q.1.isLt; omega)

theorem lc_snd (hd : HDims n k s) (Q : Sq k) (r : ℕ) {c : ℕ} (hc : c < s) :
    (lc (n := n) s Q r c).2.val = Q.2.val * s + c :=
  mkCell_snd (by have := hd.band_le Q.2.isLt; omega)

theorem lc_div (hd : HDims n k s) (Q : Sq k) {r c : ℕ} (hr : r < s) (hc : c < s) :
    (lc (n := n) s Q r c).1.val / s = Q.1.val ∧ (lc (n := n) s Q r c).1.val % s = r ∧
      (lc (n := n) s Q r c).2.val / s = Q.2.val ∧ (lc (n := n) s Q r c).2.val % s = c := by
  rw [lc_fst hd Q c hr, lc_snd hd Q r hc]
  exact ⟨(divmod hr).1, (divmod hr).2, (divmod hc).1, (divmod hc).2⟩

theorem lc_inj (hd : HDims n k s) (Q : Sq k) {r c r' c' : ℕ} (hr : r < s) (hc : c < s)
    (hr' : r' < s) (hc' : c' < s) (h : lc (n := n) s Q r c = lc s Q r' c') : r = r' ∧ c = c' := by
  have e1 := congrArg (fun x : Cell n => x.1.val) h
  have e2 := congrArg (fun x : Cell n => x.2.val) h
  simp only [lc_fst hd Q _ hr, lc_fst hd Q _ hr', lc_snd hd Q _ hc, lc_snd hd Q _ hc'] at e1 e2
  omega

theorem lc_ne (hd : HDims n k s) (Q : Sq k) {r c r' c' : ℕ} (hr : r < s) (hc : c < s)
    (hr' : r' < s) (hc' : c' < s) (h : r ≠ r' ∨ c ≠ c') : lc (n := n) s Q r c ≠ lc s Q r' c' :=
  fun e => by have := lc_inj hd Q hr hc hr' hc' e; omega

/-- Every cell of a square is a local cell. -/
theorem eq_lc (hd : HDims n k s) (x : Cell n) :
    x = lc s (sqOf hd x) (x.1.val % s) (x.2.val % s) := by
  have hs := hd.s_pos
  have h1 := Nat.div_add_mod x.1.val s
  have h2 := Nat.div_add_mod x.2.val s
  apply SlidingPuzzle.Hub.cell_ext
  · rw [lc_fst hd _ _ (Nat.mod_lt _ hs)]; simp only [sqOf]; rw [mul_comm]; omega
  · rw [lc_snd hd _ _ (Nat.mod_lt _ hs)]; simp only [sqOf]; rw [mul_comm]; omega

/-- A local position of a port box is a region cell of that port. -/
theorem rkey_box (pd : PDims n k s q σ) (Q : Sq k) {pt : Pt} {r c : ℕ}
    (h : inBox k s σ pt r c) :
    rkey L s σ pd.hd (lc (n := n) s Q r c) = some (Q, some pt) := by
  have hf := pd.fit
  have hq := pd.td.q_le
  have hrc : r < s ∧ c < s := by cases pt <;> simp only [inBox] at h <;> omega
  obtain ⟨d1, d2, d3, d4⟩ := lc_div (n := n) pd.hd Q hrc.1 hrc.2
  obtain ⟨hr, hc⟩ := not_lane_of_box pd h
  rw [rkey_eq_some]
  refine ⟨⟨d1, d3, ?_⟩, ?_⟩
  · unfold LaneCell
    rw [d2, d4]
    rintro (⟨h1, -⟩ | ⟨-, h1, -⟩) <;> omega
  · rw [d2, d4, partOf_eq_some pd hrc.1 hrc.2]; exact Or.inl h

omit [NeZero n] in
/-- A region cell on a port's line belongs to that port. -/
theorem rkey_line (pd : PDims n k s q σ) {Q : Sq k} {pt : Pt} {x : Cell n}
    (hx : region L s Q x) (h : onLine k s q pt (x.1.val % s) (x.2.val % s)) :
    rkey L s σ pd.hd x = some (Q, some pt) := by
  have hs := pd.hd.s_pos
  rw [rkey_eq_some]
  exact ⟨hx, (partOf_eq_some pd (Nat.mod_lt _ hs) (Nat.mod_lt _ hs)).2 (Or.inr h)⟩

omit [NeZero n] in
/-- A region cell outside the ports belongs to the main part. -/
theorem rkey_main (pd : PDims n k s q σ) {Q : Sq k} {x : Cell n}
    (hx : region L s Q x) (h : ∀ pt, ¬ PortLoc k s q σ pt (x.1.val % s) (x.2.val % s)) :
    rkey L s σ pd.hd x = some (Q, none) := by
  rw [rkey_eq_some]
  exact ⟨hx, partOf_eq_none.2 h⟩

end local_cells

/-! ## Counts by part -/

/-- Nonblank class-`y` tiles in part `p` of square `Q`. -/
noncomputable def pcount (s σ : ℕ) (hd : HDims n k s) (B : Board n) (Q : Sq k) (p : Part)
    (y : Sq k) : ℕ :=
  kcount (rkey L s σ hd) hd B (some (Q, p)) y

theorem regionCount_eq_kcount (hd : HDims n k s) (B : Board n) (Q y : Sq k) :
    regionCount L hd B Q y = kcount (key L hd) hd B (some Q) y := by
  unfold regionCount kcount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [key_eq_some]

/-- The region count is the sum of the counts of its parts. -/
theorem regionCount_eq_sum (hd : HDims n k s) (B : Board n) (Q y : Sq k) :
    regionCount L hd B Q y = ∑ p : Part, pcount L s σ hd B Q p y := by
  rw [regionCount_eq_kcount]
  have e : key L hd = fun x => Option.map Prod.fst (rkey L s σ hd x) :=
    funext fun x => (rkey_fst L hd x).symm
  rw [e, kcount_comp (rkey L s σ hd) (Option.map Prod.fst) hd B (some Q) y]
  unfold pcount
  symm
  refine Finset.sum_bij (fun p _ => some (Q, p)) ?_ ?_ ?_ ?_
  · intro p _; simp
  · intro p _ p' _ h; simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h; exact h
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases a with _ | ⟨Q', p⟩
    · simp at ha
    · simp only [Option.map_some, Option.some.injEq] at ha
      exact ⟨p, Finset.mem_univ _, by rw [ha]⟩
  · intro p _; rfl

end SlidingPuzzle.Port
