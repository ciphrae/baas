import SlidingPuzzle.Tree.LayoutFacts

/-! # Region counts under board changes

`keyOf x` is the square whose region contains the cell `x` (or `none` for a
corridor cell). Region counts only depend on the keys of the tiles' cells, so
it suffices to know which tiles change their key (`KeepKey`). -/
namespace SlidingPuzzle.Tree
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf incCnt decCnt)

variable {n k s q : ℕ} (L : LaneSys k q)

theorem position_eq_of_apply {C : Board n} {x : Cell n} {t : Tile n} (h : C x = t) :
    position C t = x := by
  rw [← h]; simp [position]

section
variable [NeZero n]

/-- The predicate counted by `regionCount`, on tiles. -/
def TileIn (hd : HDims n k s) (B : Board n) (Q y : Sq k) (t : Tile n) : Prop :=
  t.val ≠ 0 ∧ classOf hd t = y ∧ key L hd (position B t) = some Q

omit [NeZero n] in
theorem regionCount_eq_tiles (hd : HDims n k s) (B : Board n) (Q y : Sq k) :
    regionCount L hd B Q y =
      (Finset.univ.filter fun t => TileIn L hd B Q y t).card := by
  classical
  unfold regionCount
  convert Finset.card_equiv B _ using 2
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, TileIn, position,
    Equiv.symm_apply_apply, key_eq_some L hd]
  tauto

/-- All nonblank tiles outside `M` keep the key of their cell. -/
def KeepKey (hd : HDims n k s) (B C : Board n) (M : Finset (Tile n)) : Prop :=
  ∀ t : Tile n, t.val ≠ 0 → t ∉ M → key L hd (position C t) = key L hd (position B t)

omit [NeZero n] in
theorem KeepKey.refl (hd : HDims n k s) (B : Board n) (M : Finset (Tile n)) :
    KeepKey L hd B B M := fun _ _ _ => rfl

omit [NeZero n] in
variable {L} in
theorem KeepKey.trans {hd : HDims n k s} {B C D : Board n} {M N : Finset (Tile n)}
    (h1 : KeepKey L hd B C M) (h2 : KeepKey L hd C D N) : KeepKey L hd B D (M ∪ N) := by
  classical
  intro t ht htM
  rw [Finset.mem_union, not_or] at htM
  rw [h2 t ht htM.2, h1 t ht htM.1]

omit [NeZero n] in
variable {L} in
theorem KeepKey.mono {hd : HDims n k s} {B C : Board n} {M N : Finset (Tile n)}
    (h : KeepKey L hd B C M) (hMN : M ⊆ N) : KeepKey L hd B C N :=
  fun t ht htN => h t ht (fun h' => htN (hMN h'))

omit [NeZero n] in
variable {L} in
theorem KeepKey.erase {hd : HDims n k s} {B C : Board n} {M : Finset (Tile n)}
    (h : KeepKey L hd B C M) (t : Tile n)
    (ht : t.val ≠ 0 → key L hd (position C t) = key L hd (position B t)) :
    KeepKey L hd B C (M.erase t) := by
  intro t' ht' htM
  by_cases e : t' = t
  · subst e; exact ht ht'
  · exact h t' ht' (fun hm => htM (Finset.mem_erase.mpr ⟨e, hm⟩))

omit [NeZero n] in
/-- Agreement outside a set of cells of one key keeps every key. -/
theorem keepKey_of_agree (hd : HDims n k s) {B C : Board n} (U : Cell n → Prop)
    (hU : ∀ x y, U x → U y → key L hd x = key L hd y)
    (hC : ∀ x, ¬ U x → C x = B x) : KeepKey L hd B C ∅ := by
  intro t _ _
  have hx : B (position B t) = t := B.apply_symm_apply t
  by_cases hu : U (position B t)
  · by_cases hu' : U (position C t)
    · exact hU _ _ hu' hu
    · exfalso
      have h1 : C (position C t) = t := C.apply_symm_apply t
      rw [hC _ hu'] at h1
      have : position B t = position C t := position_eq_of_apply h1
      exact hu' (this ▸ hu)
  · have : C (position B t) = t := by rw [hC _ hu, hx]
    rw [position_eq_of_apply this]

omit [NeZero n] in
/-- Agreement outside a finite set of cells: only the tiles there may change keys. -/
theorem keepKey_of_agree_outside (hd : HDims n k s) {B C : Board n} (U : Finset (Cell n))
    (hC : ∀ x, x ∉ U → C x = B x) : KeepKey L hd B C (U.image B) := by
  classical
  intro t _ htU
  have hx : B (position B t) = t := B.apply_symm_apply t
  have hu : position B t ∉ U := fun h => htU (Finset.mem_image.mpr ⟨_, h, hx⟩)
  have : C (position B t) = t := by rw [hC _ hu, hx]
  rw [position_eq_of_apply this]

/-- A walk of the blank along cells `f 0, …, f d` (every tile moves back one
cell) keeps all keys except possibly that of the tile crossing step `j`. -/
theorem keepKey_of_walk (hd : HDims n k s) {B C : Board n} (f : ℕ → Cell n) (d j : ℕ)
    (hb : blank B = f 0)
    (hkey : ∀ t, t < d → t ≠ j → key L hd (f t) = key L hd (f (t+1)))
    (hC : ∀ t, t < d → C (f t) = B (f (t+1)))
    (hfix : ∀ x, (∀ t, t ≤ d → x ≠ f t) → C x = B x) :
    KeepKey L hd B C {B (f (j+1))} := by
  intro T hT hTj
  rw [Finset.mem_singleton] at hTj
  have hx : B (position B T) = T := B.apply_symm_apply T
  by_cases hon : ∃ t, t ≤ d ∧ position B T = f t
  · obtain ⟨t, htd, ht⟩ := hon
    rcases t with _ | u
    · exfalso
      apply hT
      rw [← hx, ht, ← hb]
      simp [blank, position]
    · have hCu : C (f u) = T := by rw [hC u (by omega), ← ht, hx]
      have hpos : position C T = f u := position_eq_of_apply hCu
      rw [hpos, ht]
      apply hkey u (by omega)
      rintro rfl
      exact hTj (by rw [← hx, ht])
  · push Not at hon
    have : C (position B T) = T := by
      rw [hfix _ (fun t ht h => hon t ht h), hx]
    rw [position_eq_of_apply this]

/-- The count identity behind `KeepKey`. -/
theorem regionCount_keepKey (hd : HDims n k s) {B C : Board n} {M : Finset (Tile n)}
    (h : KeepKey L hd B C M) (Q y : Sq k) :
    regionCount L hd C Q y + (M.filter fun t => TileIn L hd B Q y t).card =
      regionCount L hd B Q y + (M.filter fun t => TileIn L hd C Q y t).card := by
  classical
  rw [regionCount_eq_tiles, regionCount_eq_tiles]
  have hsplit : ∀ X : Board n, (Finset.univ.filter fun t => TileIn L hd X Q y t).card =
      (M.filter fun t => TileIn L hd X Q y t).card +
        ((Finset.univ \ M).filter fun t => TileIn L hd X Q y t).card := by
    intro X
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_sdiff]
      tauto
    · rw [Finset.disjoint_left]
      intro t h1 h2
      simp only [Finset.mem_filter, Finset.mem_sdiff] at h1 h2
      exact h2.1.2 h1.1
  have hout : ((Finset.univ \ M).filter fun t => TileIn L hd C Q y t) =
      ((Finset.univ \ M).filter fun t => TileIn L hd B Q y t) := by
    apply Finset.filter_congr
    intro t ht
    have hm : t ∉ M := (Finset.mem_sdiff.mp ht).2
    unfold TileIn
    constructor
    · rintro ⟨h0, hc, hk⟩
      exact ⟨h0, hc, by rw [← h t h0 hm]; exact hk⟩
    · rintro ⟨h0, hc, hk⟩
      exact ⟨h0, hc, by rw [h t h0 hm]; exact hk⟩
  rw [hsplit C, hsplit B, hout]
  omega

omit [NeZero n] in
theorem incCnt_apply {c : Sq k → Sq k → ℕ} {Q y Q' y' : Sq k} :
    incCnt c Q y Q' y' = c Q' y' + (if Q' = Q ∧ y' = y then 1 else 0) := by
  unfold incCnt; split_ifs <;> simp

/-- Two tiles change keys: `t1` enters region `h` from a corridor, `t2` leaves
region `S` into a corridor. -/
theorem regionCount_move2 (hd : HDims n k s) {B C : Board n} {t1 t2 : Tile n}
    (h : KeepKey L hd B C {t1, t2}) (h12 : t1 ≠ t2) (h1 : t1.val ≠ 0) (h2 : t2.val ≠ 0)
    {S hq : Sq k} (hS : S ≠ hq)
    (k1B : key L hd (position B t1) = none) (k1C : key L hd (position C t1) = some hq)
    (k2B : key L hd (position B t2) = some S) (k2C : key L hd (position C t2) = none)
    (Q y : Sq k) :
    regionCount L hd C Q y =
      incCnt (decCnt (regionCount L hd B) S (classOf hd t2)) hq (classOf hd t1) Q y := by
  classical
  have e := regionCount_keepKey L hd h Q y
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_pair h12, Finset.sum_pair h12] at e
  simp only [TileIn, k1B, k1C, k2B, k2C, reduceCtorEq, and_false, if_false, Option.some.injEq,
    h1, h2, ne_eq, not_false_eq_true, true_and] at e
  unfold incCnt decCnt
  have hne : (hq = Q ∧ classOf hd t1 = y) → ¬ (S = Q ∧ classOf hd t2 = y) := by
    rintro ⟨rfl, -⟩ ⟨h', -⟩; exact hS h'
  by_cases a1 : Q = hq ∧ y = classOf hd t1 <;> by_cases a2 : Q = S ∧ y = classOf hd t2 <;>
    simp only [a1, a2, and_self, if_true, if_false] at e ⊢ <;>
    split_ifs at e <;> simp_all <;> omega

/-- One tile moves from region `Z` to region `E`. -/
theorem regionCount_move1 (hd : HDims n k s) {B C : Board n} {t1 : Tile n}
    (h : KeepKey L hd B C {t1}) (h1 : t1.val ≠ 0) {Z E : Sq k} (hZE : Z ≠ E)
    (k1B : key L hd (position B t1) = some Z) (k1C : key L hd (position C t1) = some E)
    (Q y : Sq k) :
    regionCount L hd C Q y =
      incCnt (decCnt (regionCount L hd B) Z (classOf hd t1)) E (classOf hd t1) Q y := by
  classical
  have e := regionCount_keepKey L hd h Q y
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_singleton,
    Finset.sum_singleton] at e
  simp only [TileIn, k1B, k1C, Option.some.injEq, h1, ne_eq, not_false_eq_true,
    true_and] at e
  unfold incCnt decCnt
  by_cases a1 : Q = E ∧ y = classOf hd t1 <;> by_cases a2 : Q = Z ∧ y = classOf hd t1 <;>
    simp only [a1, a2, and_self, if_true, if_false] at e ⊢ <;>
    split_ifs at e <;> simp_all <;> omega

end

end SlidingPuzzle.Tree

namespace SlidingPuzzle.Tree
open SlidingPuzzle.Hub (Sq HDims sqOf classOf reservoir InBox)

variable {n k s q : ℕ} (L : LaneSys k q)

theorem regionCount_congr (hd : HDims n k s) {B C : Board n} {Q : Sq k}
    (h : ∀ x, region L s Q x → C x = B x) (y : Sq k) :
    regionCount L hd C Q y = regionCount L hd B Q y := by
  unfold regionCount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h x h1]; exact h2⟩

theorem exists_of_regionCount (hd : HDims n k s) (B : Board n) {Q y : Sq k}
    (h : 1 ≤ regionCount L hd B Q y) :
    ∃ t : Cell n, region L s Q t ∧ (B t).val ≠ 0 ∧ classOf hd (B t) = y := by
  unfold regionCount at h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h)
  exact ⟨t, (Finset.mem_filter.mp ht).2⟩

theorem inBox_of_region (hd : HDims n k s) {Q : Sq k} {x : Cell n} (h : region L s Q x) :
    InBox (Q.1.val * s) (Q.2.val * s) s x := by
  obtain ⟨h1, h2, -⟩ := h
  have a := (Hub.div_eq_iff_bounds hd.s_pos).mp h1
  have b := (Hub.div_eq_iff_bounds hd.s_pos).mp h2
  unfold InBox; omega

end SlidingPuzzle.Tree
