import SlidingPuzzle.Tree.Count

/-! # Counting tiles by a key of their cells

For any key `κ` on cells, `kcount κ B a y` counts the nonblank class-`y` tiles of
`B` on cells of key `a`. It only depends on which tiles change their key between
two boards (`KeepK`), as `Tree.regionCount` does for the region key. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims classOf)
open SlidingPuzzle.Tree (position_eq_of_apply)

variable {n k s : ℕ} {β : Type*} (κ : Cell n → β)

/-- Nonblank class-`y` tiles on cells of key `a`. -/
noncomputable def kcount (hd : HDims n k s) (B : Board n) (a : β) (y : Sq k) : ℕ :=
  (Finset.univ.filter fun x : Cell n => κ x = a ∧ (B x).val ≠ 0 ∧ classOf hd (B x) = y).card

/-- The predicate counted by `kcount`, on tiles. -/
def KTileIn (hd : HDims n k s) (B : Board n) (a : β) (y : Sq k) (t : Tile n) : Prop :=
  t.val ≠ 0 ∧ classOf hd t = y ∧ κ (position B t) = a

theorem kcount_eq_tiles (hd : HDims n k s) (B : Board n) (a : β) (y : Sq k) :
    kcount κ hd B a y = (Finset.univ.filter fun t => KTileIn κ hd B a y t).card := by
  unfold kcount
  refine Finset.card_bij (fun x _ => B x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hp : position B (B x) = x := B.symm_apply_apply x
    exact ⟨hx.2.1, hx.2.2, by rw [hp]; exact hx.1⟩
  · intro x _ x' _ h; exact B.injective h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hB : B (position B t) = t := B.apply_symm_apply t
    refine ⟨position B t, ?_, hB⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hB]; exact ⟨ht.2.2, ht.1, ht.2.1⟩

/-- All nonblank tiles outside `M` keep the key of their cell. -/
def KeepK (B C : Board n) (M : Finset (Tile n)) : Prop :=
  ∀ t : Tile n, t.val ≠ 0 → t ∉ M → κ (position C t) = κ (position B t)

variable {κ}

theorem KeepK.refl (B : Board n) (M : Finset (Tile n)) : KeepK κ B B M := fun _ _ _ => rfl

theorem KeepK.trans {B C D : Board n} {M N : Finset (Tile n)}
    (h1 : KeepK κ B C M) (h2 : KeepK κ C D N) : KeepK κ B D (M ∪ N) := by
  intro t ht htM
  rw [Finset.mem_union, not_or] at htM
  rw [h2 t ht htM.2, h1 t ht htM.1]

theorem KeepK.mono {B C : Board n} {M N : Finset (Tile n)}
    (h : KeepK κ B C M) (hMN : M ⊆ N) : KeepK κ B C N :=
  fun t ht htN => h t ht (fun h' => htN (hMN h'))

variable (κ)

/-- Agreement outside a set of cells of one key keeps every key. -/
theorem keepK_of_agree {B C : Board n} (U : Cell n → Prop)
    (hU : ∀ x y, U x → U y → κ x = κ y) (hC : ∀ x, ¬ U x → C x = B x) : KeepK κ B C ∅ := by
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

/-- Agreement outside a finite set of cells: only the tiles there may change keys. -/
theorem keepK_of_agree_outside {B C : Board n} (U : Finset (Cell n))
    (hC : ∀ x, x ∉ U → C x = B x) : KeepK κ B C (U.image B) := by
  intro t _ htU
  have hx : B (position B t) = t := B.apply_symm_apply t
  have hu : position B t ∉ U := fun h => htU (Finset.mem_image.mpr ⟨_, h, hx⟩)
  have : C (position B t) = t := by rw [hC _ hu, hx]
  rw [position_eq_of_apply this]

/-- A walk of the blank along cells `f 0, …, f d` keeps all keys except possibly
that of the tile crossing step `j`. -/
theorem keepK_of_walk [NeZero n] {B C : Board n} (f : ℕ → Cell n) (d j : ℕ) (hb : blank B = f 0)
    (hkey : ∀ t, t < d → t ≠ j → κ (f t) = κ (f (t+1)))
    (hC : ∀ t, t < d → C (f t) = B (f (t+1)))
    (hfix : ∀ x, (∀ t, t ≤ d → x ≠ f t) → C x = B x) :
    KeepK κ B C {B (f (j+1))} := by
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

/-- The count identity behind `KeepK`: counts change only through the tiles of `M`. -/
theorem kcount_keepK (hd : HDims n k s) {B C : Board n} {M : Finset (Tile n)}
    (h : KeepK κ B C M) (a : β) (y : Sq k) :
    kcount κ hd C a y + (M.filter fun t => KTileIn κ hd B a y t).card =
      kcount κ hd B a y + (M.filter fun t => KTileIn κ hd C a y t).card := by
  rw [kcount_eq_tiles, kcount_eq_tiles]
  have hsplit : ∀ X : Board n, (Finset.univ.filter fun t => KTileIn κ hd X a y t).card =
      (M.filter fun t => KTileIn κ hd X a y t).card +
        ((Finset.univ \ M).filter fun t => KTileIn κ hd X a y t).card := by
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
  have hout : ((Finset.univ \ M).filter fun t => KTileIn κ hd C a y t) =
      ((Finset.univ \ M).filter fun t => KTileIn κ hd B a y t) := by
    apply Finset.filter_congr
    intro t ht
    have hm : t ∉ M := (Finset.mem_sdiff.mp ht).2
    unfold KTileIn
    constructor
    · rintro ⟨h0, hc, hk⟩
      exact ⟨h0, hc, by rw [← h t h0 hm]; exact hk⟩
    · rintro ⟨h0, hc, hk⟩
      exact ⟨h0, hc, by rw [h t h0 hm]; exact hk⟩
  rw [hsplit C, hsplit B, hout]
  omega

/-- Counts only depend on the cells of the key. -/
theorem kcount_congr (hd : HDims n k s) {B C : Board n} {a : β}
    (h : ∀ x, κ x = a → C x = B x) (y : Sq k) : kcount κ hd C a y = kcount κ hd B a y := by
  unfold kcount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h x h1]; exact h2⟩

/-- A positive count gives a tile of that class on a cell of the key. -/
theorem exists_of_kcount (hd : HDims n k s) (B : Board n) {a : β} {y : Sq k}
    (h : 1 ≤ kcount κ hd B a y) :
    ∃ t : Cell n, κ t = a ∧ (B t).val ≠ 0 ∧ classOf hd (B t) = y := by
  unfold kcount at h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h)
  exact ⟨t, (Finset.mem_filter.mp ht).2⟩

/-- A count above the size of a set of cells gives a tile outside the set. -/
theorem exists_of_kcount_avoid (hd : HDims n k s) (B : Board n) {a : β} {y : Sq k}
    (F : Finset (Cell n)) (h : F.card + 1 ≤ kcount κ hd B a y) :
    ∃ t : Cell n, t ∉ F ∧ κ t = a ∧ (B t).val ≠ 0 ∧ classOf hd (B t) = y := by
  unfold kcount at h
  set S := Finset.univ.filter fun x : Cell n => κ x = a ∧ (B x).val ≠ 0 ∧ classOf hd (B x) = y
    with hS
  have h1 := Finset.le_card_sdiff F S
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (show 0 < (S \ F).card by omega)
  rw [Finset.mem_sdiff, hS, Finset.mem_filter] at ht
  exact ⟨t, ht.2, ht.1.2⟩

/-- Counts through a key coarsening `g`: the coarse count is the sum of the fine counts
over the fiber. -/
theorem kcount_comp [Fintype β] [DecidableEq β] {γ : Type*} [DecidableEq γ] (g : β → γ)
    (hd : HDims n k s) (B : Board n) (c : γ) (y : Sq k) :
    kcount (fun x => g (κ x)) hd B c y =
      ∑ a ∈ Finset.univ.filter (fun a => g a = c), kcount κ hd B a y := by
  unfold kcount
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp
  · intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact hab (h1.2.1.symm.trans h2.2.1)

end SlidingPuzzle.Port
