import Zhong.Algorithm.Parberry
import Zhong.Algorithm.StripPlace

/-!
# The row-by-row assembly (M7, Parberry)

`Algorithm/StripPlace.lean` places a tile that already lies in the active `2 × m` strip.
This file assembles the row-by-row reduction-of-order algorithm: each step normalises the
blank to the lower row of the strip, raises the required tile into the strip (if it lies
below), and places it into the current target cell.  Every step costs `O(n + m)` moves and
fixes the already-placed cells, so a row costs `O(n²)` and the whole board `O(n³)`.
-/

namespace Zhong

open Equiv

variable {n m : ℕ}

local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin m))
local notation "d(" a "," b ")" => ((⟨a, by omega⟩ : Fin 2), (⟨b, by omega⟩ : Fin m))

/-- **Board form of `stripPlace`.**  If the blank sits at `hStrip p` (with `p` in the lower
row) and the tile with label `T` sits at `hStrip a`, then an `O(m)`-move word places `T` at
`hStrip c` while fixing all cells above the strip and every cell of the strip's upper row
left of the target. -/
lemma stripPlaceBoard {r : ℕ} (hr : r + 1 < n) (hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 4 ≤ m)
    {B : Board n m}
    [NeZero (n * m)] {p a c : Cell 2 m} {T : Fin (n * m)}
    (hblank : blank B = hStrip (m := m) r hr p)
    (htile : B (hStrip (m := m) r hr a) = T)
    (hp : p.1.val = 1) (hc : c.1.val = 0) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 0 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val) :
    ∃ σ : List Dir, ApplicableFrom (blank B) σ ∧
      (actSeq B σ) (hStrip (m := m) r hr c) = T ∧
      (∀ z : Cell n m, z.1.val < r → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.1.val = r → z.2.val < c.2.val → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.2.val < lo → (actSeq B σ) z = B z) ∧
      σ.length ≤ 96 * m + 8 := by
  obtain ⟨σ, hapσ, hperm, hfix1, hfix2, hfix3, _, hlen⟩ :=
    stripPlace r hr hm lo hlo hp hc hpa hac hrow hplo halo hclo
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [hblank]; exact hapσ
  · rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hperm, htile]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix1 z hz]
  · intro z hz hzc
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix2 z hz hzc]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix3 z hz]

/-- **Board form of `stripPlace` with the clean-workspace bound.**  In addition to the
conclusion of `stripPlaceBoard`, the placement fixes every cell of the strip's *lower* row
outside the workspace window `[lo, lo + 4)`, except the blank cell and the tile's original
cell.  This is the "clean placement" property recorded in `NOTES_M8.md`: when the blank and the
tile both lie inside a single `R` block `[lo, lo + 4)` of a data row, the placement leaves
every `V` cell of that row untouched (the `R` cells are don't-cares). -/
lemma stripPlaceBoard_fix {r : ℕ} (hr : r + 1 < n) (hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 4 ≤ m)
    {B : Board n m}
    [NeZero (n * m)] {p a c : Cell 2 m} {T : Fin (n * m)}
    (hblank : blank B = hStrip (m := m) r hr p)
    (htile : B (hStrip (m := m) r hr a) = T)
    (hp : p.1.val = 1) (hc : c.1.val = 0) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 0 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val) :
    ∃ σ : List Dir, ApplicableFrom (blank B) σ ∧
      (actSeq B σ) (hStrip (m := m) r hr c) = T ∧
      (∀ z : Cell n m, z.1.val < r → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.1.val = r → z.2.val < c.2.val → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.2.val < lo → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.1.val = r + 1 →
          (z.2.val < lo ∨ lo + 4 ≤ z.2.val) →
          z ≠ hStrip (m := m) r hr p → z ≠ hStrip (m := m) r hr a →
          (actSeq B σ) z = B z) ∧
      σ.length ≤ 96 * m + 8 := by
  obtain ⟨σ, hapσ, hperm, hfix1, hfix2, hfix3, hfix4, hlen⟩ :=
    stripPlace r hr hm lo hlo hp hc hpa hac hrow hplo halo hclo
  have hzcell : ∀ z : Cell n m, z.1.val = r + 1 →
      z = hStrip (m := m) r hr (((1 : Fin 2), z.2) : Cell 2 m) := by
    intro z hzr
    apply Prod.ext
    · apply Fin.ext
      simp only [hStrip, Prod.fst, Fin.val_mk]
      omega
    · rfl
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [hblank]; exact hapσ
  · rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hperm, htile]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix1 z hz]
  · intro z hz hzc
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix2 z hz hzc]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix3 z hz]
  · intro z hzr hzw hzp hza
    have hcell := hzcell z hzr
    have h2 : (((1 : Fin 2), z.2) : Cell 2 m) ≠ p := by
      intro h; exact hzp (by rw [hcell, h])
    have h3 : (((1 : Fin 2), z.2) : Cell 2 m) ≠ a := by
      intro h; exact hza (by rw [hcell, h])
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank]
    conv_lhs => rw [hcell]
    rw [hfix4 z.2 hzw h2 h3, ← hcell]

/-- **Clean placement protecting a prescribed set of lower-row cells.**  If the blank and the
tile both lie inside the workspace window `[lo, lo + 4)`, and a set `Vc` of lower-row cells is
disjoint from that window and from the blank and tile cells, then the placement of
`stripPlaceBoard` fixes every cell of `Vc`.  This is the form in which the scratch-row repair
uses the primitive: `Vc` is the set of `V` cells of the data row below the repaired `H` row,
and the workspace window is a single `R` block. -/
lemma stripPlaceBoard_fix_protected {r : ℕ} (hr : r + 1 < n) (hm : 4 ≤ m) (lo : ℕ)
    (hlo : lo + 4 ≤ m)
    {B : Board n m}
    [NeZero (n * m)] {p a c : Cell 2 m} {T : Fin (n * m)} {Vc : Finset (Cell n m)}
    (hblank : blank B = hStrip (m := m) r hr p)
    (htile : B (hStrip (m := m) r hr a) = T)
    (hp : p.1.val = 1) (hc : c.1.val = 0) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 0 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (hptu : p.2.val < lo + 4)
    (halo : lo ≤ a.2.val) (hatu : a.2.val < lo + 4) (hclo : lo ≤ c.2.val)
    (hVrow : ∀ z ∈ Vc, z.1.val = r + 1)
    (hVwin : ∀ z ∈ Vc, z.2.val < lo ∨ lo + 4 ≤ z.2.val)
    (hVp : ∀ z ∈ Vc, z ≠ hStrip (m := m) r hr p)
    (hVa : ∀ z ∈ Vc, z ≠ hStrip (m := m) r hr a) :
    ∃ σ : List Dir, ApplicableFrom (blank B) σ ∧
      (actSeq B σ) (hStrip (m := m) r hr c) = T ∧
      (∀ z ∈ Vc, (actSeq B σ) z = B z) ∧
      σ.length ≤ 96 * m + 8 := by
  obtain ⟨σ, hapσ, hplace, _, _, _, hfixV, hlen⟩ :=
    stripPlaceBoard_fix hr hm lo hlo hblank htile hp hc hpa hac hrow hplo halo hclo
  refine ⟨σ, hapσ, hplace, ?_, hlen⟩
  intro z hz
  exact hfixV z (hVrow z hz) (hVwin z hz) (hVp z hz) (hVa z hz)

/-- **Board form of `stripPlaceFlip`.**  The blank sits at `hStrip p` with `p` in the *upper*
row and the tile with label `T` sits at `hStrip a`; an `O(m)`-move word places `T` at
`hStrip c` (in the lower row) while fixing all cells above the strip and every cell of the
strip's lower row left of the target. -/
lemma stripPlaceFlipBoard {r : ℕ} (hr : r + 1 < n) (hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 4 ≤ m)
    {B : Board n m}
    [NeZero (n * m)] {p a c : Cell 2 m} {T : Fin (n * m)}
    (hblank : blank B = hStrip (m := m) r hr p)
    (htile : B (hStrip (m := m) r hr a) = T)
    (hp : p.1.val = 0) (hc : c.1.val = 1) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 1 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val) :
    ∃ σ : List Dir, ApplicableFrom (blank B) σ ∧
      (actSeq B σ) (hStrip (m := m) r hr c) = T ∧
      (∀ z : Cell n m, z.1.val < r → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.1.val = r + 1 → z.2.val < c.2.val → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.2.val < lo → (actSeq B σ) z = B z) ∧
      σ.length ≤ 96 * m + 8 := by
  obtain ⟨σ, hapσ, hperm, hfix1, hfix2, hfix3, hlen⟩ :=
    stripPlaceFlip r hr hm lo hlo hp hc hpa hac hrow hplo halo hclo
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [hblank]; exact hapσ
  · rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hperm, htile]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix1 z hz]
  · intro z hz hzc
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix2 z hz hzc]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix3 z hz]

/-- **Board form of `stripPlace2`.**  The two-row variant of `stripPlaceBoard`: the frontier is
the target column, the auxiliaries may lie in either row, and an extra cell `J` is avoided. -/
lemma stripPlace2Board {r : ℕ} (hr : r + 1 < n) (hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 3 ≤ m)
    {B : Board n m}
    [NeZero (n * m)] {p a c J : Cell 2 m} {T : Fin (n * m)} (hlo_eq : c.2.val = lo)
    (hblank : blank B = hStrip (m := m) r hr p)
    (htile : B (hStrip (m := m) r hr a) = T)
    (hp : p.1.val = 1) (hc : c.1.val = 0) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 0 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val) :
    ∃ σ : List Dir, ApplicableFrom (blank B) σ ∧
      (actSeq B σ) (hStrip (m := m) r hr c) = T ∧
      (∀ z : Cell n m, z.1.val < r → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.1.val = r → z.2.val < c.2.val → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.2.val < lo → (actSeq B σ) z = B z) ∧
      σ.length ≤ 96 * m + 8 := by
  obtain ⟨σ, hapσ, hperm, hfix1, hfix2, hfix3, hlen⟩ :=
    stripPlace2 (J := J) r hr hm lo hlo hlo_eq hp hc hpa hac hrow hplo halo hclo
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [hblank]; exact hapσ
  · rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hperm, htile]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix1 z hz]
  · intro z hz hzc
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix2 z hz hzc]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix3 z hz]

/-- **Board form of `stripPlaceFlip2`.** -/
lemma stripPlaceFlip2Board {r : ℕ} (hr : r + 1 < n) (hm : 4 ≤ m) (lo : ℕ) (hlo : lo + 3 ≤ m)
    {B : Board n m}
    [NeZero (n * m)] {p a c J : Cell 2 m} {T : Fin (n * m)} (hlo_eq : c.2.val = lo)
    (hblank : blank B = hStrip (m := m) r hr p)
    (htile : B (hStrip (m := m) r hr a) = T)
    (hp : p.1.val = 0) (hc : c.1.val = 1) (hpa : p ≠ a) (hac : a ≠ c)
    (hrow : a.1.val = 1 → c.2.val ≤ a.2.val)
    (hplo : lo ≤ p.2.val) (halo : lo ≤ a.2.val) (hclo : lo ≤ c.2.val)
    (hJp : J ≠ p) (hJa : J ≠ a) (hJc : J ≠ c) :
    ∃ σ : List Dir, ApplicableFrom (blank B) σ ∧
      (actSeq B σ) (hStrip (m := m) r hr c) = T ∧
      (∀ z : Cell n m, z.1.val < r → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.1.val = r + 1 → z.2.val < c.2.val → (actSeq B σ) z = B z) ∧
      (∀ z : Cell n m, z.2.val < lo → (actSeq B σ) z = B z) ∧
      (actSeq B σ) (hStrip (m := m) r hr J) = B (hStrip (m := m) r hr J) ∧
      σ.length ≤ 96 * m + 8 := by
  obtain ⟨σ, hapσ, hperm, hfix1, hfix2, hfix3, hJfix, hlen⟩ :=
    stripPlaceFlip2 (J := J) r hr hm lo hlo hlo_eq hp hc hpa hac hrow hplo halo hclo
      hJp hJa hJc
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [hblank]; exact hapσ
  · rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hperm, htile]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix1 z hz]
  · intro z hz hzc
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix2 z hz hzc]
  · intro z hz
    rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hfix3 z hz]
  · rw [actSeq_eq_permOf, Equiv.trans_apply, hblank, hJfix]

/-- **One placement step**, assuming the blank already sits in the lower row at `(r+1,0)`.

If rows `< r` and row `r` up to column `yc` already agree with the target, then the tile
belonging to `(r,yc)` can be placed there with an `O(n + m)`-move word that fixes all the
previously placed cells. -/
theorem placeStepFromNormal (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 < n) (hm : 4 ≤ m)
    (lo : ℕ) (hlo : lo + 4 ≤ m)
    (B : Board n m) [NeZero (n * m)] (yc : ℕ) (hyc : yc < m)
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hcol : ∀ (x : Fin n) (y : Fin m), y.val < lo → B (x,y) = target n m (x,y))
    (hleft : ∀ (y : Fin m), y.val < yc →
      B ((⟨r, by omega⟩ : Fin n), y) = target n m ((⟨r, by omega⟩ : Fin n), y))
    (hyclo : lo ≤ yc)
    (y0 : ℕ) (hy0 : y0 < m) (hy0lo : lo ≤ y0) (hblank : blank B = c(r+1,y0)) :
    ∃ σ : List Dir,
      (actSeq B σ) c(r,yc) = target n m c(r,yc) ∧
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (x : Fin n) (y : Fin m), y.val < lo → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (y : Fin m), y.val < yc →
        (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
          = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
      σ.length ≤ 250 * (n + m) := by
  classical
  set T : Fin (n * m) := target n m c(r,yc) with hT
  set a : Cell n m := B.symm T with ha
  have hBa : B a = T := Equiv.apply_symm_apply B T
  have hT0 : T ≠ 0 := by
    rw [hT]; exact target_ne_zero r yc hyc (by omega)
  have hane : a ≠ blank B := by
    intro h
    have h1 : B a = 0 := by rw [h]; exact Equiv.apply_symm_apply B 0
    rw [hBa] at h1
    exact hT0 h1
  have hstrip0 : hStrip (m := m) r hr (d(1,y0)) = c(r+1,y0) := by simp [hStrip, bot]
  have hstripc : hStrip (m := m) r hr (d(0,yc)) = c(r,yc) := by simp [hStrip, top]
  have halo : lo ≤ a.2.val := by
    by_contra h
    have h1 : B a = target n m a := hcol a.1 a.2 (by omega)
    have h3 : a = c(r,yc) := (target n m).injective (h1.symm.trans hBa)
    have := congrArg (fun w : Cell n m => w.2.val) h3
    simp only [Fin.val_mk] at this
    omega
  by_cases hsame : a = c(r,yc)
  · refine ⟨[], ?_, ?_, ?_, ?_, by simp⟩
    · rw [actSeq_nil, ← hsame, hBa, hT]
    · intro x y hx; rw [actSeq_nil]; exact habove x y hx
    · intro x y hy; rw [actSeq_nil]; exact hcol x y hy
    · intro y hy; rw [actSeq_nil]; exact hleft y hy
  · have ha_row : r ≤ a.1.val := by
      by_contra h
      have h1 : B a = target n m a := habove a.1 a.2 (by omega)
      have h3 : a = c(r,yc) := (target n m).injective (h1.symm.trans hBa)
      exact hsame h3
    have ha_col : a.1.val = r → yc ≤ a.2.val := by
      intro har
      by_contra h
      have ha_eq : a = ((⟨r, by omega⟩ : Fin n), a.2) := by
        apply Prod.ext
        · exact Fin.ext har
        · rfl
      have h1 : B a = target n m a := by
        rw [ha_eq]; exact hleft a.2 (by omega)
      have h3 : a = c(r,yc) := (target n m).injective (h1.symm.trans hBa)
      have := congrArg (fun w : Cell n m => w.2.val) h3
      simp only [Fin.val_mk] at this
      omega
    rcases (by omega : a.1.val ≥ r + 2 ∨ a.1.val = r + 1 ∨ a.1.val = r) with har2 | har1 | har0
    · -- tile strictly below the strip: raise it into the strip, then place
      have hxa : a.1.val < n := a.1.isLt
      have hya : a.2.val < m := a.2.isLt
      by_cases ha2 : a.2.val + 1 < m
      · obtain ⟨σr, happr, htrr, heffr, hfixr, hcolr, hlenr⟩ :=
          raiseTile r (r+1) y0 a.1.val a.2.val hxa hr hya ha2 hy0 (by omega) har2
            (le_rfl) (by intro h; omega)
        have hfixrcol : ∀ z : Cell n m, z.2.val < lo → permOf c(r+1,y0) σr z = z :=
          permOf_fixes_of_traceSet_col (lo := lo) (fun z hz => by
            obtain ⟨h1, _⟩ := hcolr z hz
            omega)
        have hstripq : hStrip (m := m) r hr (d(1, a.2.val + 1)) = c(r+1, a.2.val+1) := by
          simp [hStrip, bot]
        have hstripA : hStrip (m := m) r hr (d(1, a.2.val)) = c(r+1, a.2.val) := by
          simp [hStrip, bot]
        have hblank' : blank (actSeq B σr) = hStrip (m := m) r hr (d(1, a.2.val + 1)) := by
          rw [blank_actSeq, hblank, htrr, hstripq]
        have htile' : (actSeq B σr) (hStrip (m := m) r hr (d(1, a.2.val))) = T := by
          rw [hstripA, actSeq_eq_permOf, hblank, Equiv.trans_apply, heffr]
          simpa using hBa
        have hpne : d(1, a.2.val + 1) ≠ d(1, a.2.val) := by
          intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
          simp only [Fin.val_mk] at this; omega
        have hac' : d(1, a.2.val) ≠ d(0, yc) := by
          intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
          simp only [Fin.val_mk] at this; omega
        obtain ⟨σp, hapσp, heffσp, hfix1, hfix2, hfix3, hlenp⟩ :=
          stripPlaceBoard hr hm lo hlo hblank' htile' (by simp) (by simp) hpne hac'
            (by intro h; simp only [Prod.fst, Fin.val_mk] at h; omega)
            (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
            (by simp only [Fin.val_mk]; omega)
        refine ⟨σr ++ σp, ?_, ?_, ?_, ?_, by rw [List.length_append]; omega⟩
        · rw [actSeq_append, ← hstripc]; exact heffσp
        · intro x y hx
          rw [actSeq_append, hfix1 (x,y) hx,
            actSeq_eq_permOf, hblank, Equiv.trans_apply,
            hfixr (x,y) (by simp only [Fin.val_mk]; omega)]
          exact habove x y hx
        · intro x y hy
          rw [actSeq_append, hfix3 (x,y) hy,
            actSeq_eq_permOf, hblank, Equiv.trans_apply, hfixrcol (x,y) hy]
          exact hcol x y hy
        · intro y hy
          rw [actSeq_append, hfix2 ((⟨r, by omega⟩ : Fin n), y) rfl hy,
            actSeq_eq_permOf, hblank, Equiv.trans_apply,
            hfixr ((⟨r, by omega⟩ : Fin n), y) (by simp only [Fin.val_mk]; omega)]
          exact hleft y hy
      · have hya2lo : lo ≤ a.2.val - 1 := by omega
        have hypos : 0 < a.2.val := by omega
        obtain ⟨σr, happr, htrr, heffr, hfixr, hfixrcol, hlenr⟩ :=
          raiseTileLeft r (r+1) y0 a.1.val a.2.val hxa hr hya hy0 (by omega) hypos
            har2 (le_rfl) (by intro h; omega) lo hy0lo hya2lo
        have hstripq : hStrip (m := m) r hr (d(1, a.2.val - 1)) = c(r+1, a.2.val-1) := by
          simp [hStrip, bot]
        have hstripA : hStrip (m := m) r hr (d(1, a.2.val)) = c(r+1, a.2.val) := by
          simp [hStrip, bot]
        have hblank' : blank (actSeq B σr) = hStrip (m := m) r hr (d(1, a.2.val - 1)) := by
          rw [blank_actSeq, hblank, htrr, hstripq]
        have htile' : (actSeq B σr) (hStrip (m := m) r hr (d(1, a.2.val))) = T := by
          rw [hstripA, actSeq_eq_permOf, hblank, Equiv.trans_apply, heffr]
          simpa using hBa
        have hpne : d(1, a.2.val - 1) ≠ d(1, a.2.val) := by
          intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
          simp only [Fin.val_mk] at this; omega
        have hac' : d(1, a.2.val) ≠ d(0, yc) := by
          intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
          simp only [Fin.val_mk] at this; omega
        obtain ⟨σp, hapσp, heffσp, hfix1, hfix2, hfix3, hlenp⟩ :=
          stripPlaceBoard hr hm lo hlo hblank' htile' (by simp) (by simp) hpne hac'
            (by intro h; simp only [Prod.fst, Fin.val_mk] at h; omega)
            (by simp only [Fin.val_mk]; exact hya2lo)
            (by simp only [Fin.val_mk]; exact halo)
            (by simp only [Fin.val_mk]; exact hyclo)
        refine ⟨σr ++ σp, ?_, ?_, ?_, ?_, by rw [List.length_append]; omega⟩
        · rw [actSeq_append, ← hstripc]; exact heffσp
        · intro x y hx
          rw [actSeq_append, hfix1 (x,y) hx,
            actSeq_eq_permOf, hblank, Equiv.trans_apply,
            hfixr (x,y) (by simp only [Fin.val_mk]; omega)]
          exact habove x y hx
        · intro x y hy
          rw [actSeq_append, hfix3 (x,y) hy,
            actSeq_eq_permOf, hblank, Equiv.trans_apply, hfixrcol (x,y) hy]
          exact hcol x y hy
        · intro y hy
          rw [actSeq_append, hfix2 ((⟨r, by omega⟩ : Fin n), y) rfl hy,
            actSeq_eq_permOf, hblank, Equiv.trans_apply,
            hfixr ((⟨r, by omega⟩ : Fin n), y) (by simp only [Fin.val_mk]; omega)]
          exact hleft y hy
    · -- tile in the lower row of the strip
      have hstripA : hStrip (m := m) r hr (d(1, a.2.val)) = a := by
        apply Prod.ext
        · apply Fin.ext; simp only [hStrip, Prod.fst, Fin.val_mk]; omega
        · rfl
      have hblank' : blank B = hStrip (m := m) r hr (d(1,y0)) := by rw [hblank, hstrip0]
      have htile' : B (hStrip (m := m) r hr (d(1, a.2.val))) = T := by rw [hstripA]; exact hBa
      have hpne : d(1,y0) ≠ d(1, a.2.val) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
        simp only [Fin.val_mk] at this
        exact hane (by
          rw [hblank]
          apply Prod.ext
          · exact Fin.ext (by omega)
          · exact Fin.ext this.symm)
      have hac' : d(1, a.2.val) ≠ d(0, yc) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
        simp only [Fin.val_mk] at this; omega
      obtain ⟨σ, hapσ, heffσ, hfix1, hfix2, hfix3, hlen⟩ :=
        stripPlaceBoard hr hm lo hlo hblank' htile' (by simp) (by simp) hpne hac'
          (by intro h; simp only [Prod.fst, Fin.val_mk] at h; omega) (by simp only [Fin.val_mk]; exact hy0lo) (by simp only [Fin.val_mk]; exact halo) (by simp only [Fin.val_mk]; exact hyclo)
      refine ⟨σ, ?_, ?_, ?_, ?_, by omega⟩
      · rw [← hstripc]; exact heffσ
      · intro x y hx
        rw [hfix1 (x,y) hx]
        exact habove x y hx
      · intro x y hy
        rw [hfix3 (x,y) hy]
        exact hcol x y hy
      · intro y hy
        rw [hfix2 ((⟨r, by omega⟩ : Fin n), y) rfl hy]
        exact hleft y hy
    · -- tile in the upper row of the strip
      have hstripA : hStrip (m := m) r hr (d(0, a.2.val)) = a := by
        apply Prod.ext
        · apply Fin.ext; simp only [hStrip, Prod.fst, Fin.val_mk]; omega
        · rfl
      have hblank' : blank B = hStrip (m := m) r hr (d(1,y0)) := by rw [hblank, hstrip0]
      have htile' : B (hStrip (m := m) r hr (d(0, a.2.val))) = T := by rw [hstripA]; exact hBa
      have hpne : d(1,y0) ≠ d(0, a.2.val) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
        simp only [Fin.val_mk] at this; omega
      have hac' : d(0, a.2.val) ≠ d(0, yc) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
        simp only [Fin.val_mk] at this
        exact hsame (by
          apply Prod.ext
          · exact Fin.ext (by omega)
          · exact Fin.ext this)
      have hrow : (d(0, a.2.val)).1.val = 0 → yc ≤ a.2.val := by
        intro _; exact ha_col har0
      obtain ⟨σ, hapσ, heffσ, hfix1, hfix2, hfix3, hlen⟩ :=
        stripPlaceBoard hr hm lo hlo hblank' htile' (by simp) (by simp) hpne hac' hrow (by simp only [Fin.val_mk]; exact hy0lo) (by simp only [Fin.val_mk]; exact halo) (by simp only [Fin.val_mk]; exact hyclo)
      refine ⟨σ, ?_, ?_, ?_, ?_, by omega⟩
      · rw [← hstripc]; exact heffσ
      · intro x y hx
        rw [hfix1 (x,y) hx]
        exact habove x y hx
      · intro x y hy
        rw [hfix3 (x,y) hy]
        exact hcol x y hy
      · intro y hy
        rw [hfix2 ((⟨r, by omega⟩ : Fin n), y) rfl hy]
        exact hleft y hy


/-- **One placement step**, with the blank normalised first.  The frontier `lo` records
the columns `< lo` that are already solved; the normalisation is vertical so the blank keeps
its (active) column, and every operation stays in columns `≥ lo`. -/
theorem placeStep (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 < n) (hm : 4 ≤ m)
    (lo : ℕ) (hlo : lo + 4 ≤ m)
    (B : Board n m) [NeZero (n * m)] (yc : ℕ) (hyc : yc < m)
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hcol : ∀ (x : Fin n) (y : Fin m), y.val < lo → B (x,y) = target n m (x,y))
    (hleft : ∀ (y : Fin m), y.val < yc →
      B ((⟨r, by omega⟩ : Fin n), y) = target n m ((⟨r, by omega⟩ : Fin n), y))
    (hyclo : lo ≤ yc) :
    ∃ σ : List Dir,
      (actSeq B σ) ((⟨r, by omega⟩ : Fin n), (⟨yc, hyc⟩ : Fin m))
        = target n m ((⟨r, by omega⟩ : Fin n), (⟨yc, hyc⟩ : Fin m)) ∧
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (x : Fin n) (y : Fin m), y.val < lo → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (y : Fin m), y.val < yc →
        (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
          = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
      σ.length ≤ 251 * (n + m) := by
  classical
  set p0 : Cell n m := blank B with hp0
  have hp0row : r ≤ p0.1.val := by
    by_contra h
    have h1 : B p0 = target n m p0 := habove p0.1 p0.2 (by omega)
    have h2 : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
    rw [h1] at h2
    exact target_ne_zero p0.1.val p0.2.val p0.2.isLt (by omega) h2
  have hp0lo : lo ≤ p0.2.val := by
    by_contra h
    have h1 : B p0 = target n m p0 := hcol p0.1 p0.2 (by omega)
    have h2 : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
    have h3 : target n m p0 = 0 := by rw [← h1, h2]
    have hlast := target_last (n := n) (m := m) (by omega) (by omega) (by nlinarith)
    have hcell : p0 = (((⟨n-1, by omega⟩ : Fin n), (⟨m-1, by omega⟩ : Fin m)) : Cell n m) :=
      (target n m).injective (h3.trans hlast.symm)
    have := congrArg (fun w : Cell n m => w.2.val) hcell
    simp only [Fin.val_mk] at this
    omega
  set σ0 : List Dir := moveXWord p0.1.val (r+1) with hσ0
  have happ0 : ApplicableFrom p0 σ0 := by
    rw [hσ0]
    exact applicableFrom_moveXWord p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt
  have htr0 : trace p0 σ0
      = ((⟨r+1, by omega⟩ : Fin n), (⟨p0.2.val, p0.2.isLt⟩ : Fin m)) := by
    rw [hσ0]
    have := trace_moveXWord p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt
    simpa using this
  have hbound : ∀ z ∈ traceSet p0 σ0,
      z.2 = p0.2 ∧ min p0.1.val (r+1) ≤ z.1.val ∧ z.1.val ≤ max p0.1.val (r+1) := by
    intro z hz
    rw [hσ0] at hz
    exact moveXWord_traceSet p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt z hz
  have hfix0 : ∀ z : Cell n m, z.1.val < r → permOf p0 σ0 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨_, hmin, _⟩ := hbound z hmem
    omega
  have hfix0col : ∀ z : Cell n m, z.2.val < lo → permOf p0 σ0 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨h2, _, _⟩ := hbound z hmem
    omega
  have hfix0' : ∀ z : Cell n m, z.1.val = r → z.2.val < yc → permOf p0 σ0 z = z := by
    intro z hzr hzc
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    obtain ⟨h2, hmin, hmax⟩ := hbound z hmem
    have hp0r : p0.1.val = r := by omega
    have hz2 : p0.2.val < yc := by rw [← h2]; exact hzc
    have hBp0 : B p0 = target n m p0 := by
      have : p0 = ((⟨r, by omega⟩ : Fin n), p0.2) := by
        apply Prod.ext
        · exact Fin.ext hp0r
        · rfl
      rw [this]; exact hleft p0.2 (by omega)
    have hzero : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
    have hcell : p0 = ((⟨r, by omega⟩ : Fin n), (⟨p0.2.val, p0.2.isLt⟩ : Fin m)) := by
      apply Prod.ext
      · exact Fin.ext hp0r
      · rfl
    rw [hBp0] at hzero
    exact target_ne_zero r p0.2.val p0.2.isLt (by omega) (by rw [← hcell]; exact hzero)
  have hblank0 : blank (actSeq B σ0)
      = ((⟨r+1, by omega⟩ : Fin n), (⟨p0.2.val, p0.2.isLt⟩ : Fin m)) := by
    rw [blank_actSeq, ← hp0, htr0]
  have habove0 : ∀ (x : Fin n) (y : Fin m), x.val < r →
      (actSeq B σ0) (x,y) = target n m (x,y) := by
    intro x y hx
    rw [actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0 (x,y) hx]
    exact habove x y hx
  have hcol0 : ∀ (x : Fin n) (y : Fin m), y.val < lo →
      (actSeq B σ0) (x,y) = target n m (x,y) := by
    intro x y hy
    rw [actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0col (x,y) hy]
    exact hcol x y hy
  have hleft0 : ∀ (y : Fin m), y.val < yc →
      (actSeq B σ0) ((⟨r, by omega⟩ : Fin n), y)
        = target n m ((⟨r, by omega⟩ : Fin n), y) := by
    intro y hy
    rw [actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0' ((⟨r, by omega⟩ : Fin n), y) rfl hy]
    exact hleft y hy
  obtain ⟨σ1, heff1, habove1, hcol1, hleft1, hlen1⟩ :=
    placeStepFromNormal r hr hr2 hm lo hlo (actSeq B σ0) yc hyc habove0 hcol0 hleft0 hyclo
      p0.2.val p0.2.isLt hp0lo hblank0
  refine ⟨σ0 ++ σ1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [actSeq_append]; exact heff1
  · intro x y hx; rw [actSeq_append]; exact habove1 x y hx
  · intro x y hy; rw [actSeq_append]; exact hcol1 x y hy
  · intro y hy; rw [actSeq_append]; exact hleft1 y hy
  · rw [List.length_append]
    have hlen0 : σ0.length ≤ n + m := by
      rw [hσ0, length_moveXWord]
      have h1 : Nat.dist p0.1.val (r+1) ≤ n := by
        rw [Nat.dist_eq_max_sub_min]; omega
      omega
    omega


/-- **Row assembly.**  Given a board whose rows above `r` already agree with the target,
place the whole `r`-th row using `O(m²)` moves.  The induction is on the number of columns
still to place; each step uses `placeStep`. -/
theorem solveRowAux (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 < n) (hm : 4 ≤ m)
    (lo : ℕ) (hlo : lo + 4 ≤ m) :
    ∀ (k : ℕ), ∀ (j : ℕ), m - j = k → lo ≤ j → j ≤ m →
      ∀ (B : Board n m) [NeZero (n * m)],
        (∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y)) →
        (∀ (x : Fin n) (y : Fin m), y.val < lo → B (x,y) = target n m (x,y)) →
        (∀ (y : Fin m), y.val < j →
          B ((⟨r, by omega⟩ : Fin n), y) = target n m ((⟨r, by omega⟩ : Fin n), y)) →
        ∃ σ : List Dir,
          (∀ (x : Fin n) (y : Fin m), x.val < r →
            (actSeq B σ) (x,y) = target n m (x,y)) ∧
          (∀ (x : Fin n) (y : Fin m), y.val < lo →
            (actSeq B σ) (x,y) = target n m (x,y)) ∧
          (∀ (y : Fin m), (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
            = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
          σ.length ≤ (m - j) * (251 * (n + m)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hk hloj hj B _ habove hcol hleft
    by_cases hjm : j < m
    · obtain ⟨σ1, heff1, habove1, hcol1, hleft1, hlen1⟩ :=
        placeStep r hr hr2 hm lo hlo B j hjm habove hcol (fun y hy => hleft y hy) hloj
      have hleft2 : ∀ (y : Fin m), y.val < j + 1 →
          (actSeq B σ1) ((⟨r, by omega⟩ : Fin n), y)
            = target n m ((⟨r, by omega⟩ : Fin n), y) := by
        intro y hy
        rcases (by omega : y.val < j ∨ y.val = j) with h | h
        · exact hleft1 y h
        · have hy' : y = (⟨j, hjm⟩ : Fin m) := Fin.ext h
          rw [hy']; exact heff1
      obtain ⟨σ2, habove2, hcol2, hall2, hlen2⟩ :=
        ih (m - (j+1)) (by omega) (j+1) (by omega) (by omega) (by omega) (actSeq B σ1)
          habove1 hcol1 hleft2
      refine ⟨σ1 ++ σ2, ?_, ?_, ?_, ?_⟩
      · simpa [actSeq_append] using habove2
      · simpa [actSeq_append] using hcol2
      · simpa [actSeq_append] using hall2
      · rw [List.length_append]
        have hmj : m - j = m - (j+1) + 1 := by omega
        calc σ1.length + σ2.length
            ≤ 251 * (n + m) + (m - (j+1)) * (251 * (n + m)) := add_le_add hlen1 hlen2
          _ = (m - j) * (251 * (n + m)) := by rw [hmj]; ring
    · have hjm' : j = m := by omega
      refine ⟨[], ?_, ?_, ?_, by simp⟩
      · exact habove
      · exact hcol
      · intro y
        rw [actSeq_nil]
        exact hleft y (by rw [hjm']; exact y.isLt)

/-- **Row assembly.**  Solves row `r` for all columns `≥ lo`, fixing rows `< r` and columns
`< lo`, in `O((m-lo)·(n+m))` moves. -/
theorem solveRow (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 < n) (hm : 4 ≤ m)
    (lo : ℕ) (hlo : lo + 4 ≤ m)
    (B : Board n m) [NeZero (n * m)]
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hcol : ∀ (x : Fin n) (y : Fin m), y.val < lo → B (x,y) = target n m (x,y)) :
    ∃ σ : List Dir,
      (∀ (x : Fin n) (y : Fin m), x.val < r →
        (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (x : Fin n) (y : Fin m), y.val < lo →
        (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (y : Fin m), (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
        = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
      σ.length ≤ (m - lo) * (251 * (n + m)) := by
  obtain ⟨σ, h1, h2, h3, h4⟩ :=
    solveRowAux r hr hr2 hm lo hlo (m - lo) lo rfl le_rfl (by omega) B habove hcol
      (fun y hy => hcol (⟨r, by omega⟩ : Fin n) y hy)
  exact ⟨σ, h1, h2, h3, h4⟩


/-- **One placement step on the last strip** (no row below): the tile is already in the
strip, so no raise is needed. -/
theorem placeStepStrip (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m)
    (B : Board n m) [NeZero (n * m)] (yc : ℕ) (hyc : yc < m)
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hleft : ∀ (y : Fin m), y.val < yc →
      B ((⟨r, by omega⟩ : Fin n), y) = target n m ((⟨r, by omega⟩ : Fin n), y))
    (hblank : blank B = c(r+1,0)) :
    ∃ σ : List Dir,
      (actSeq B σ) c(r,yc) = target n m c(r,yc) ∧
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (y : Fin m), y.val < yc →
        (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
          = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
      σ.length ≤ 250 * (n + m) := by
  classical
  set T : Fin (n * m) := target n m c(r,yc) with hT
  set a : Cell n m := B.symm T with ha
  have hBa : B a = T := Equiv.apply_symm_apply B T
  have hT0 : T ≠ 0 := by
    rw [hT]; exact target_ne_zero r yc hyc (by omega)
  have hane : a ≠ blank B := by
    intro h
    have h1 : B a = 0 := by rw [h]; exact Equiv.apply_symm_apply B 0
    rw [hBa] at h1
    exact hT0 h1
  have hstrip0 : hStrip (m := m) r hr (d(1,0)) = c(r+1,0) := by simp [hStrip, bot]
  have hstripc : hStrip (m := m) r hr (d(0,yc)) = c(r,yc) := by simp [hStrip, top]
  by_cases hsame : a = c(r,yc)
  · refine ⟨[], ?_, ?_, ?_, by simp⟩
    · rw [actSeq_nil, ← hsame, hBa, hT]
    · intro x y hx; rw [actSeq_nil]; exact habove x y hx
    · intro y hy; rw [actSeq_nil]; exact hleft y hy
  · have ha_row : r ≤ a.1.val := by
      by_contra h
      have h1 : B a = target n m a := habove a.1 a.2 (by omega)
      have h3 : a = c(r,yc) := (target n m).injective (h1.symm.trans hBa)
      exact hsame h3
    have ha_col : a.1.val = r → yc ≤ a.2.val := by
      intro har
      by_contra h
      have ha_eq : a = ((⟨r, by omega⟩ : Fin n), a.2) := by
        apply Prod.ext
        · exact Fin.ext har
        · rfl
      have h1 : B a = target n m a := by
        rw [ha_eq]; exact hleft a.2 (by omega)
      have h3 : a = c(r,yc) := (target n m).injective (h1.symm.trans hBa)
      have := congrArg (fun w : Cell n m => w.2.val) h3
      simp only [Fin.val_mk] at this
      omega
    rcases (by omega : a.1.val = r + 1 ∨ a.1.val = r) with har1 | har0
    · -- tile in the lower row of the strip
      have hstripA : hStrip (m := m) r hr (d(1, a.2.val)) = a := by
        apply Prod.ext
        · apply Fin.ext; simp only [hStrip, Prod.fst, Fin.val_mk]; omega
        · rfl
      have hblank' : blank B = hStrip (m := m) r hr (d(1,0)) := by rw [hblank, hstrip0]
      have htile' : B (hStrip (m := m) r hr (d(1, a.2.val))) = T := by rw [hstripA]; exact hBa
      have hpne : d(1,0) ≠ d(1, a.2.val) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
        simp only [Fin.val_mk] at this
        exact hane (by
          rw [hblank]
          apply Prod.ext
          · exact Fin.ext (by omega)
          · exact Fin.ext this.symm)
      have hac' : d(1, a.2.val) ≠ d(0, yc) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
        simp only [Fin.val_mk] at this; omega
      obtain ⟨σ, hapσ, heffσ, hfix1, hfix2, hlen⟩ :=
        stripPlaceBoard hr hm 0 (by omega) hblank' htile' (by simp) (by simp) hpne hac'
          (by intro h; simp only [Prod.fst, Fin.val_mk] at h; omega) (by omega) (by omega) (by omega)
      refine ⟨σ, ?_, ?_, ?_, by omega⟩
      · rw [← hstripc]; exact heffσ
      · intro x y hx
        rw [hfix1 (x,y) hx]
        exact habove x y hx
      · intro y hy
        rw [hfix2 ((⟨r, by omega⟩ : Fin n), y) rfl hy]
        exact hleft y hy
    · -- tile in the upper row of the strip
      have hstripA : hStrip (m := m) r hr (d(0, a.2.val)) = a := by
        apply Prod.ext
        · apply Fin.ext; simp only [hStrip, Prod.fst, Fin.val_mk]; omega
        · rfl
      have hblank' : blank B = hStrip (m := m) r hr (d(1,0)) := by rw [hblank, hstrip0]
      have htile' : B (hStrip (m := m) r hr (d(0, a.2.val))) = T := by rw [hstripA]; exact hBa
      have hpne : d(1,0) ≠ d(0, a.2.val) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.1.val) h
        simp only [Fin.val_mk] at this; omega
      have hac' : d(0, a.2.val) ≠ d(0, yc) := by
        intro h; have := congrArg (fun w : Cell 2 m => w.2.val) h
        simp only [Fin.val_mk] at this
        exact hsame (by
          apply Prod.ext
          · exact Fin.ext (by omega)
          · exact Fin.ext this)
      have hrow : (d(0, a.2.val)).1.val = 0 → yc ≤ a.2.val := by
        intro _; exact ha_col har0
      obtain ⟨σ, hapσ, heffσ, hfix1, hfix2, hlen⟩ :=
        stripPlaceBoard hr hm 0 (by omega) hblank' htile' (by simp) (by simp) hpne hac' hrow (by omega) (by omega) (by omega)
      refine ⟨σ, ?_, ?_, ?_, by omega⟩
      · rw [← hstripc]; exact heffσ
      · intro x y hx
        rw [hfix1 (x,y) hx]
        exact habove x y hx
      · intro y hy
        rw [hfix2 ((⟨r, by omega⟩ : Fin n), y) rfl hy]
        exact hleft y hy


theorem placeStepStripNorm (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m)
    (B : Board n m) [NeZero (n * m)] (yc : ℕ) (hyc : yc < m)
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y))
    (hleft : ∀ (y : Fin m), y.val < yc →
      B ((⟨r, by omega⟩ : Fin n), y) = target n m ((⟨r, by omega⟩ : Fin n), y)) :
    ∃ σ : List Dir,
      (actSeq B σ) ((⟨r, by omega⟩ : Fin n), (⟨yc, hyc⟩ : Fin m))
        = target n m ((⟨r, by omega⟩ : Fin n), (⟨yc, hyc⟩ : Fin m)) ∧
      (∀ (x : Fin n) (y : Fin m), x.val < r → (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (y : Fin m), y.val < yc →
        (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
          = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
      σ.length ≤ 251 * (n + m) := by
  classical
  set p0 : Cell n m := blank B with hp0
  have hp0row : r ≤ p0.1.val := by
    by_contra h
    have h1 : B p0 = target n m p0 := habove p0.1 p0.2 (by omega)
    have h2 : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
    rw [h1] at h2
    exact target_ne_zero p0.1.val p0.2.val p0.2.isLt (by omega) h2
  set σ0 : List Dir := moveToWord p0.1.val p0.2.val (r+1) 0 with hσ0
  have happ0 : ApplicableFrom p0 σ0 := by
    rw [hσ0]
    have := applicableFrom_moveToWord p0.1.val p0.2.val (r+1) 0 (by omega) (by omega)
      p0.1.isLt p0.2.isLt
    simpa using this
  have htr0 : trace p0 σ0 = ((⟨r+1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) := by
    rw [hσ0]
    have := trace_moveToWord p0.1.val p0.2.val (r+1) 0 (by omega) (by omega)
      p0.1.isLt p0.2.isLt
    simpa using this
  have hbound : ∀ z ∈ traceSet p0 σ0,
      (z.2 = p0.2 ∧ min p0.1.val (r+1) ≤ z.1.val ∧ z.1.val ≤ max p0.1.val (r+1))
        ∨ z.1.val = r + 1 := by
    intro z hz
    rw [hσ0, show moveToWord p0.1.val p0.2.val (r+1) 0
        = moveXWord p0.1.val (r+1) ++ moveYWord p0.2.val 0 from rfl,
      traceSet_append] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · left
      exact moveXWord_traceSet p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt z hz
    · right
      rw [trace_moveXWord p0.1.val p0.2.val (r+1) (by omega) p0.1.isLt p0.2.isLt] at hz
      exact congrArg Fin.val (moveYWord_traceSet (r+1) p0.2.val 0 (by omega) (by omega)
        p0.2.isLt z hz)
  have hfix0 : ∀ z : Cell n m, z.1.val < r → permOf p0 σ0 z = z := by
    intro z hz
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    rcases hbound z hmem with ⟨h2, hmin, hmax⟩ | h
    · omega
    · omega
  have hfix0' : ∀ z : Cell n m, z.1.val = r → z.2.val < yc → permOf p0 σ0 z = z := by
    intro z hzr hzc
    apply permOf_apply_of_not_mem_traceSet
    intro hmem
    rcases hbound z hmem with ⟨h2, hmin, hmax⟩ | h
    · have hp0r : p0.1.val = r := by omega
      have hz2 : p0.2.val < yc := by rw [← h2]; exact hzc
      have hBp0 : B p0 = target n m p0 := by
        have : p0 = ((⟨r, by omega⟩ : Fin n), p0.2) := by
          apply Prod.ext
          · exact Fin.ext hp0r
          · rfl
        rw [this]; exact hleft p0.2 (by omega)
      have hzero : B p0 = 0 := by rw [hp0]; exact Equiv.apply_symm_apply B 0
      have hcell : p0 = ((⟨r, by omega⟩ : Fin n), (⟨p0.2.val, p0.2.isLt⟩ : Fin m)) := by
        apply Prod.ext
        · exact Fin.ext hp0r
        · rfl
      rw [hBp0] at hzero
      exact target_ne_zero r p0.2.val p0.2.isLt (by omega) (by rw [← hcell]; exact hzero)
    · omega
  have hblank0 : blank (actSeq B σ0) = ((⟨r+1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin m)) := by
    rw [blank_actSeq, ← hp0, htr0]
  have habove0 : ∀ (x : Fin n) (y : Fin m), x.val < r →
      (actSeq B σ0) (x,y) = target n m (x,y) := by
    intro x y hx
    rw [actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0 (x,y) hx]
    exact habove x y hx
  have hleft0 : ∀ (y : Fin m), y.val < yc →
      (actSeq B σ0) ((⟨r, by omega⟩ : Fin n), y)
        = target n m ((⟨r, by omega⟩ : Fin n), y) := by
    intro y hy
    rw [actSeq_eq_permOf, Equiv.trans_apply, ← hp0, hfix0' ((⟨r, by omega⟩ : Fin n), y) rfl hy]
    exact hleft y hy
  obtain ⟨σ1, heff1, habove1, hleft1, hlen1⟩ :=
    placeStepStrip r hr hr2 hm (actSeq B σ0) yc hyc habove0 hleft0 hblank0
  refine ⟨σ0 ++ σ1, ?_, ?_, ?_, ?_⟩
  · rw [actSeq_append]; exact heff1
  · intro x y hx; rw [actSeq_append]; exact habove1 x y hx
  · intro y hy; rw [actSeq_append]; exact hleft1 y hy
  · rw [List.length_append]
    have hlen0 : σ0.length ≤ n + m := by
      rw [hσ0, length_moveToWord]
      have h1 : Nat.dist p0.1.val (r+1) ≤ n := by
        rw [Nat.dist_eq_max_sub_min]; omega
      have h2 : Nat.dist p0.2.val 0 ≤ m := by
        rw [Nat.dist_eq_max_sub_min]; omega
      omega
    omega


/-- **Row assembly.**  Given a board whose rows above `r` already agree with the target,
place the whole `r`-th row using `O(m²)` moves.  The induction is on the number of columns
still to place; each step uses `placeStep`. -/

theorem solveStripAux (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m) :
    ∀ (k : ℕ), ∀ (j : ℕ), m - j = k → j ≤ m →
      ∀ (B : Board n m) [NeZero (n * m)],
        (∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y)) →
        (∀ (y : Fin m), y.val < j →
          B ((⟨r, by omega⟩ : Fin n), y) = target n m ((⟨r, by omega⟩ : Fin n), y)) →
        ∃ σ : List Dir,
          (∀ (x : Fin n) (y : Fin m), x.val < r →
            (actSeq B σ) (x,y) = target n m (x,y)) ∧
          (∀ (y : Fin m), (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
            = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
          σ.length ≤ (m - j) * (251 * (n + m)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hk hj B _ habove hleft
    by_cases hjm : j < m
    · obtain ⟨σ1, heff1, habove1, hleft1, hlen1⟩ :=
        placeStepStripNorm r hr hr2 hm B j hjm habove (fun y hy => hleft y hy)
      have hleft2 : ∀ (y : Fin m), y.val < j + 1 →
          (actSeq B σ1) ((⟨r, by omega⟩ : Fin n), y)
            = target n m ((⟨r, by omega⟩ : Fin n), y) := by
        intro y hy
        rcases (by omega : y.val < j ∨ y.val = j) with h | h
        · exact hleft1 y h
        · have hy' : y = (⟨j, hjm⟩ : Fin m) := Fin.ext h
          rw [hy']; exact heff1
      obtain ⟨σ2, habove2, hall2, hlen2⟩ :=
        ih (m - (j+1)) (by omega) (j+1) (by omega) (by omega) (actSeq B σ1) habove1 hleft2
      refine ⟨σ1 ++ σ2, ?_, ?_, ?_⟩
      · simpa [actSeq_append] using habove2
      · simpa [actSeq_append] using hall2
      · rw [List.length_append]
        have hmj : m - j = m - (j+1) + 1 := by omega
        calc σ1.length + σ2.length
            ≤ 251 * (n + m) + (m - (j+1)) * (251 * (n + m)) := add_le_add hlen1 hlen2
          _ = (m - j) * (251 * (n + m)) := by rw [hmj]; ring
    · have hjm' : j = m := by omega
      refine ⟨[], ?_, ?_, by simp⟩
      · exact habove
      · intro y
        rw [actSeq_nil]
        exact hleft y (by rw [hjm']; exact y.isLt)

/-- **Row assembly**, `j = 0` case. -/
theorem solveStrip (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 = n) (hm : 4 ≤ m)
    (B : Board n m) [NeZero (n * m)]
    (habove : ∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y)) :
    ∃ σ : List Dir,
      (∀ (x : Fin n) (y : Fin m), x.val < r →
        (actSeq B σ) (x,y) = target n m (x,y)) ∧
      (∀ (y : Fin m), (actSeq B σ) ((⟨r, by omega⟩ : Fin n), y)
        = target n m ((⟨r, by omega⟩ : Fin n), y)) ∧
      σ.length ≤ m * (251 * (n + m)) := by
  obtain ⟨σ, h1, h2, h3⟩ :=
    solveStripAux r hr hr2 hm (m - 0) 0 rfl (by omega) B habove (fun y hy => by omega)
  refine ⟨σ, h1, h2, ?_⟩
  simpa using h3



/-- **Solve the first `n-2` rows.**  Iterating `solveRow` over the rows gives a word of
`O(n³)` moves placing rows `0, …, n-3`; then `solveStrip` places row `n-2`. -/
theorem solveRows (B : Board n m) [NeZero (n * m)] (hn : 3 ≤ n) (hm : 4 ≤ m) :
    ∃ σ : List Dir,
      (∀ (x : Fin n) (y : Fin m), x.val ≤ n - 3 →
        (actSeq B σ) (x,y) = target n m (x,y)) ∧
      σ.length ≤ (n - 2) * (m * (251 * (n + m))) := by
  have key : ∀ (k : ℕ), ∀ (r : ℕ), (n - 2) - r = k → r ≤ n - 2 →
      ∀ (B : Board n m),
        (∀ (x : Fin n) (y : Fin m), x.val < r → B (x,y) = target n m (x,y)) →
        ∃ σ : List Dir,
          (∀ (x : Fin n) (y : Fin m), x.val ≤ n - 3 →
            (actSeq B σ) (x,y) = target n m (x,y)) ∧
          σ.length ≤ (n - 2 - r) * (m * (251 * (n + m))) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro r hk hr B hB
      by_cases hr' : r < n - 2
      · obtain ⟨σ1, h1, _, h2, hlen1⟩ :=
          solveRow r (by omega) (by omega) hm 0 (by omega) B hB (fun x y hy => by omega)
        have hB2 : ∀ (x : Fin n) (y : Fin m), x.val < r + 1 →
            (actSeq B σ1) (x,y) = target n m (x,y) := by
          intro x y hx
          rcases (by omega : x.val < r ∨ x.val = r) with h | h
          · exact h1 x y h
          · have hx' : x = (⟨r, by omega⟩ : Fin n) := Fin.ext h
            rw [hx']; exact h2 y
        obtain ⟨σ2, h3, hlen2⟩ :=
          ih ((n - 2) - (r+1)) (by omega) (r+1) rfl (by omega) (actSeq B σ1) hB2
        refine ⟨σ1 ++ σ2, ?_, ?_⟩
        · intro x y hx
          rw [actSeq_append]; exact h3 x y hx
        · rw [List.length_append]
          have hmj : n - 2 - r = n - 2 - (r+1) + 1 := by omega
          calc σ1.length + σ2.length
              ≤ m * (251 * (n + m)) + (n - 2 - (r+1)) * (m * (251 * (n + m))) :=
                add_le_add hlen1 hlen2
            _ = (n - 2 - r) * (m * (251 * (n + m))) := by rw [hmj]; ring
      · have hr2 : r = n - 2 := by omega
        refine ⟨[], ?_, by simp⟩
        intro x y hx
        rw [actSeq_nil]
        exact hB x y (by omega)
  obtain ⟨σ, h1, h2⟩ := key (n - 2 - 0) 0 rfl (by omega) B (fun x y hx => by omega)
  exact ⟨σ, h1, by simpa using h2⟩

/-- **Partial solver.**  Solves the first `n-1` rows of an `n × m` board in `O(n³)` moves.
The final row is a `1 × m` puzzle and is left to the caller. -/
theorem solveBoardPartial (B : Board n m) [NeZero (n * m)] (hn : 3 ≤ n) (hm : 4 ≤ m) :
    ∃ σ : List Dir,
      (∀ (x : Fin n) (y : Fin m), x.val ≤ n - 2 →
        (actSeq B σ) (x,y) = target n m (x,y)) ∧
      σ.length ≤ (n - 2) * (m * (251 * (n + m))) + m * (251 * (n + m)) := by
  obtain ⟨σ1, h1, hlen1⟩ := solveRows B hn hm
  have hB : ∀ (x : Fin n) (y : Fin m), x.val < n - 2 →
      (actSeq B σ1) (x,y) = target n m (x,y) := fun x y hx => h1 x y (by omega)
  obtain ⟨σ2, h2a, h2b, hlen2⟩ := solveStrip (n - 2) (by omega) (by omega) hm (actSeq B σ1) hB
  refine ⟨σ1 ++ σ2, ?_, ?_⟩
  · intro x y hx
    rw [actSeq_append]
    rcases (by omega : x.val ≤ n - 3 ∨ x.val = n - 2) with h | h
    · simpa [actSeq_append, h2a x y (by omega)] using h1 x y h
    · have hx' : x = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext h
      rw [hx']; exact h2b y
  · rw [List.length_append]; exact add_le_add hlen1 hlen2


/-! ### The column solver

`Algorithm/Assembly.lean` solves rows.  The row/column alternation of the reduction-of-order
algorithm also needs the transposed statement, solving *columns*.  Rather than duplicating
the row solver we transport it across the board transpose: apply `solveRow` to the board
`B'' = (transEquiv.trans B).trans π`, where `π` is the label permutation carrying the
transposed target to the target, and map the resulting word back along `transDir`. -/

section SolveCol

/-- The transposed target board. -/
noncomputable def transTarget (n : ℕ) : Board n n := (transEquiv n n).trans (target n n)

/-- The label permutation carrying the transposed target to the target. -/
noncomputable def transRelabel (n : ℕ) : Equiv.Perm (Fin (n * n)) :=
  (transTarget n).symm.trans (target n n)

theorem transTarget_apply (c : Cell n n) :
    transTarget n c = target n n (transEquiv n n c) := rfl

@[simp] theorem transEquiv_symm_apply {n m : ℕ} (c : Cell m n) :
    (transEquiv n m).symm c = (c.2, c.1) := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem blank_transEquiv_trans (B : Board n n) [NeZero (n * n)] :
    blank ((transEquiv n n).trans B) = ((blank B).2, (blank B).1) := by
  simp only [blank, Equiv.trans_apply, Equiv.symm_trans_apply, transEquiv_symm_apply]

theorem transRelabel_apply_transTarget (c : Cell n n) :
    transRelabel n (transTarget n c) = target n n c := by
  simp only [transRelabel, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem transRelabel_symm_transTarget (c : Cell n n) :
    (transRelabel n).symm (transTarget n c) = target n n c := by
  have h1 : (transRelabel n).symm = (target n n).symm.trans (transTarget n) := rfl
  rw [h1, Equiv.trans_apply]
  have h2 : (target n n).symm (transTarget n c) = transEquiv n n c := by
    rw [transTarget_apply, Equiv.symm_apply_apply]
  rw [h2, transTarget_apply, show transEquiv n n (transEquiv n n c) = c from rfl]

theorem target_symm_zero (n : ℕ) [NeZero (n * n)] (hn : 0 < n) (hnm : 1 < n * n) :
    (target n n).symm 0
      = (((⟨n - 1, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) : Cell n n) := by
  apply (target n n).injective
  rw [Equiv.apply_symm_apply]
  exact (target_last (n := n) (m := n) hn hn hnm).symm

theorem transRelabel_symm_zero (n : ℕ) [NeZero (n * n)] (hn : 0 < n) (hnm : 1 < n * n) :
    (transRelabel n).symm 0 = 0 := by
  have h := transRelabel_symm_transTarget (n := n) ((target n n).symm 0)
  rw [target_symm_zero n hn hnm] at h
  have htrans : transTarget n
      (((⟨n - 1, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) : Cell n n) = 0 := by
    rw [transTarget_apply, show transEquiv n n
        (((⟨n - 1, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) : Cell n n)
        = (((⟨n - 1, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) : Cell n n) from rfl]
    exact target_last (n := n) (m := n) hn hn hnm
  rw [htrans, target_last (n := n) (m := n) hn hn hnm] at h
  exact h

/-- **Column assembly.**  Solves column `k` of an `n × n` board (all rows `≥ k`), fixing
rows `< k` and columns `< k`, in `O((n-k)·n)` moves.  Obtained by transporting `solveRow`
across the board transpose. -/
theorem solveCol (k : ℕ) (hk : k + 2 < n) (hlo6 : k + 4 ≤ n)
    (B : Board n n) [NeZero (n * n)]
    (habove : ∀ (x y : Fin n), x.val < k → B (x,y) = target n n (x,y))
    (hcol : ∀ (x y : Fin n), y.val < k → B (x,y) = target n n (x,y)) :
    ∃ σ : List Dir,
      (∀ (x y : Fin n), x.val < k → (actSeq B σ) (x,y) = target n n (x,y)) ∧
      (∀ (x y : Fin n), y.val < k → (actSeq B σ) (x,y) = target n n (x,y)) ∧
      (∀ (x : Fin n), (actSeq B σ) (x, (⟨k, by omega⟩ : Fin n))
        = target n n (x, (⟨k, by omega⟩ : Fin n))) ∧
      σ.length ≤ (n - k) * (251 * (n + n)) := by
  classical
  have hn : 0 < n := by omega
  have hnm : 1 < n * n := by nlinarith
  set B' : Board n n := (transEquiv n n).trans B with hB'
  set B'' : Board n n := B'.trans (transRelabel n) with hB''
  have hblank'' : blank B'' = blank B' := by
    rw [hB'']
    simp only [blank, Equiv.trans_apply, Equiv.symm_trans_apply]
    rw [transRelabel_symm_zero n hn hnm]
  have habove'' : ∀ (x y : Fin n), x.val < k → B'' (x,y) = target n n (x,y) := by
    intro x y hx
    rw [hB'', hB']
    change transRelabel n (B (transEquiv n n (x,y))) = target n n (x,y)
    rw [show transEquiv n n (x,y) = (y,x) from rfl, hcol y x hx]
    rw [show target n n (y,x) = transTarget n (x,y) from rfl]
    exact transRelabel_apply_transTarget (x,y)
  have hcol'' : ∀ (x y : Fin n), y.val < k → B'' (x,y) = target n n (x,y) := by
    intro x y hy
    rw [hB'', hB']
    change transRelabel n (B (transEquiv n n (x,y))) = target n n (x,y)
    rw [show transEquiv n n (x,y) = (y,x) from rfl, habove y x hy]
    rw [show target n n (y,x) = transTarget n (x,y) from rfl]
    exact transRelabel_apply_transTarget (x,y)
  obtain ⟨σ', habove1, hcol1, hrow1, hlen⟩ :=
    solveRow k (by omega) hk (by omega) k hlo6 B'' habove'' hcol''
  have hσ : permOf (blank B) (σ'.map transDir)
      = (transEquiv n n).permCongr (permOf (transEquiv n n (blank B)) σ') := by
    have h := permOf_map (transEquiv n n) transDir (neighbor?_transEquiv)
      (transEquiv n n (blank B)) σ'
    rwa [show transEquiv n n (transEquiv n n (blank B)) = blank B from rfl] at h
  have hactB' : ∀ c : Cell n n,
      actSeq B (σ'.map transDir) c = actSeq B' σ' (transEquiv n n c) := by
    intro c
    rw [actSeq_eq_permOf, hσ, actSeq_eq_permOf, hB']
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, transEquiv_symm_apply,
      transEquiv_apply, blank_transEquiv_trans]
  have hact'' : actSeq B'' σ' = (actSeq B' σ').trans (transRelabel n) := by
    rw [actSeq_eq_permOf, actSeq_eq_permOf, hblank'', hB'']
    ext c
    rfl
  have hactB'' : ∀ c : Cell n n,
      actSeq B' σ' c = (transRelabel n).symm (actSeq B'' σ' c) := by
    intro c
    rw [hact'', Equiv.trans_apply, Equiv.symm_apply_apply]
  refine ⟨σ'.map transDir, ?_, ?_, ?_, ?_⟩
  · intro x y hx
    rw [hactB' (x,y), show transEquiv n n (x,y) = (y,x) from rfl, hactB'' (y,x),
      hcol1 y x hx]
    rw [show target n n (y,x) = transTarget n (x,y) from rfl]
    exact transRelabel_symm_transTarget (x,y)
  · intro x y hy
    rw [hactB' (x,y), show transEquiv n n (x,y) = (y,x) from rfl, hactB'' (y,x),
      habove1 y x hy]
    rw [show target n n (y,x) = transTarget n (x,y) from rfl]
    exact transRelabel_symm_transTarget (x,y)
  · intro x
    rw [hactB' (x, (⟨k, by omega⟩ : Fin n)),
      show transEquiv n n (x, (⟨k, by omega⟩ : Fin n)) = ((⟨k, by omega⟩ : Fin n), x) from rfl,
      hactB'' ((⟨k, by omega⟩ : Fin n), x), hrow1 x]
    rw [show target n n ((⟨k, by omega⟩ : Fin n), x)
        = transTarget n (x, (⟨k, by omega⟩ : Fin n)) from rfl]
    exact transRelabel_symm_transTarget (x, (⟨k, by omega⟩ : Fin n))
  · rw [List.length_map]
    exact hlen

end SolveCol

end Zhong
