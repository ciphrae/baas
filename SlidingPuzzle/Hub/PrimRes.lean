import SlidingPuzzle.Hub.Geom
import SlidingPuzzle.Hub.PrimCycle
import SlidingPuzzle.Moves.BlankAccess

/-! # Reservoir primitives

Walks of the blank inside one reservoir rectangle, the existence of a tile of
a counted class in a region, spare reservoir cells, and square boxes. -/
namespace SlidingPuzzle.Hub
open Classical

variable {n k s : ℕ} [NeZero n]

/-- Walk the blank inside the reservoir of `Q`: only reservoir cells change. -/
theorem exists_reservoir_walk (hd : HDims n k s) (B : Board n) {Q : Sq k}
    (hb : reservoir k s Q (blank B)) {e : Cell n} (he : reservoir k s Q e) :
    ∃ C : Board n, ∃ p : Path B C, blank C = e ∧ p.length ≤ 2 * s ∧
      ∀ x, ¬ reservoir k s Q x → C x = B x := by
  obtain ⟨C, p, hbC, hlen, hfix⟩ := exists_blank_access_path_preserving B e
  rw [reservoir_iff hd] at hb he
  refine ⟨C, p, hbC, ?_, ?_⟩
  · refine hlen.trans ?_
    simp only [gridDistance, Nat.dist]
    omega
  · intro x hx
    rw [reservoir_iff hd] at hx
    apply hfix
    omega

/-- A positive region count gives a tile of that class in the region. -/
theorem exists_of_regionCount (hd : HDims n k s) (B : Board n) {Q y : Sq k}
    (h : 1 ≤ regionCount hd B Q y) :
    ∃ t : Cell n, region k s Q t ∧ (B t).val ≠ 0 ∧ classOf hd (B t) = y := by
  unfold regionCount at h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h)
  exact ⟨t, (Finset.mem_filter.mp ht).2⟩

/-- A reservoir cell at row offset `ro` and column offset `co + j`, `j ≤ 2`,
avoiding two given cells. -/
theorem exists_reservoir_near (hd : HDims n k s) (Q : Sq k) {ro co : ℕ} (hro : k ≤ ro)
    (hro' : ro < s) (hco : k ≤ co) (hco' : co + 2 < s) (t w : Cell n) :
    ∃ j, j ≤ 2 ∧ reservoir k s Q (mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j)) ∧
      mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j) ≠ t ∧
      mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j) ≠ w := by
  have hb1 := hd.band_le Q.1.isLt
  have hb2 := hd.band_le Q.2.isLt
  have hr := hd.room
  have hsnd : ∀ j, j ≤ 2 → (mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j)).2.val =
      Q.2.val * s + co + j := fun j hj => mkCell_snd (by omega)
  have hres : ∀ j, j ≤ 2 → reservoir k s Q (mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j)) :=
    fun j hj => (reservoir_iff hd).mpr (by
      rw [mkCell_fst (by omega), hsnd j hj]; omega)
  have hne : ∀ i j, i ≤ 2 → j ≤ 2 → i ≠ j →
      mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + i) ≠
        mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + j) := fun i j hi hj hij =>
    cell_ne_of_snd (by rw [hsnd i hi, hsnd j hj]; omega)
  by_cases h0 : mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + 0) ≠ t ∧
      mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + 0) ≠ w
  · exact ⟨0, by omega, hres 0 (by omega), h0⟩
  by_cases h1 : mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + 1) ≠ t ∧
      mkCell n (Q.1.val * s + ro) (Q.2.val * s + co + 1) ≠ w
  · exact ⟨1, by omega, hres 1 (by omega), h1⟩
  refine ⟨2, le_rfl, hres 2 le_rfl, ?_, ?_⟩
  · intro e2
    rw [not_and_or, not_not, not_not] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact hne 0 1 (by omega) (by omega) (by omega) (h0.trans h1.symm)
    · exact hne 0 2 (by omega) le_rfl (by omega) (h0.trans e2.symm)
    · exact hne 1 2 (by omega) le_rfl (by omega) (h1.trans e2.symm)
    · exact hne 0 1 (by omega) (by omega) (by omega) (h0.trans h1.symm)
  · intro e2
    rw [not_and_or, not_not, not_not] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact hne 0 1 (by omega) (by omega) (by omega) (h0.trans h1.symm)
    · exact hne 1 2 (by omega) le_rfl (by omega) (h1.trans e2.symm)
    · exact hne 0 2 (by omega) le_rfl (by omega) (h0.trans e2.symm)
    · exact hne 0 1 (by omega) (by omega) (by omega) (h0.trans h1.symm)

/-- A spare reservoir cell two rows below the reservoir's top, avoiding `t`. -/
theorem exists_reservoir_other (hd : HDims n k s) (Q : Sq k) (t : Cell n) :
    ∃ u : Cell n, reservoir k s Q u ∧ u.1.val = Q.1.val * s + (k + 2) ∧
      u.2.val ≤ Q.2.val * s + (k + 1) ∧ u ≠ t := by
  have hb1 := hd.band_le Q.1.isLt
  have hb2 := hd.band_le Q.2.isLt
  have hr := hd.room
  let u1 : Cell n := mkCell n (Q.1.val * s + (k + 2)) (Q.2.val * s + k)
  let u2 : Cell n := mkCell n (Q.1.val * s + (k + 2)) (Q.2.val * s + (k + 1))
  have a1 : u1.1.val = Q.1.val * s + (k + 2) := mkCell_fst (by omega)
  have a2 : u1.2.val = Q.2.val * s + k := mkCell_snd (by omega)
  have b1 : u2.1.val = Q.1.val * s + (k + 2) := mkCell_fst (by omega)
  have b2 : u2.2.val = Q.2.val * s + (k + 1) := mkCell_snd (by omega)
  by_cases h : u1 = t
  · refine ⟨u2, (reservoir_iff hd).mpr (by omega), b1, by omega, ?_⟩
    rw [← h]
    exact cell_ne_of_snd (by omega)
  · exact ⟨u1, (reservoir_iff hd).mpr (by omega), a1, by omega, h⟩

omit [NeZero n] in
/-- The square box of a square contains its region. -/
theorem inBox_of_region (hd : HDims n k s) {Q : Sq k} {x : Cell n} (h : region k s Q x) :
    InBox (Q.1.val * s) (Q.2.val * s) s x := by
  have := region_bounds hd h
  unfold InBox; omega

omit [NeZero n] in
theorem inBox_of_reservoir (hd : HDims n k s) {Q : Sq k} {x : Cell n}
    (h : reservoir k s Q x) : InBox (Q.1.val * s) (Q.2.val * s) s x :=
  inBox_of_region hd (region_of_reservoir h)

/-- The blank of a board with its blank in some other cell. -/
theorem blank_eq_of_apply {B : Board n} {x : Cell n} (h : B x = 0) : blank B = x :=
  position_eq_of_apply h

theorem apply_blank (B : Board n) : B (blank B) = 0 := B.apply_symm_apply 0

theorem ne_blank_of_val {B : Board n} {x : Cell n} (h : (B x).val ≠ 0) : x ≠ blank B := by
  intro e; apply h; rw [e, apply_blank]; rfl

theorem val_ne_zero_of_ne_blank {B : Board n} {x : Cell n} (h : x ≠ blank B) : (B x).val ≠ 0 := by
  intro e
  apply h
  exact (blank_eq_of_apply (Fin.ext e)).symm

omit [NeZero n] in
/-- Region counts only depend on the region's cells. -/
theorem regionCount_congr (hd : HDims n k s) {B C : Board n} {Q : Sq k}
    (h : ∀ x, region k s Q x → C x = B x) (y : Sq k) :
    regionCount hd C Q y = regionCount hd B Q y := by
  unfold regionCount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h x h1]; exact h2⟩

end SlidingPuzzle.Hub
