import SlidingPuzzle.Tree.Simulate

/-! # The abstraction of a board and its totals -/
namespace SlidingPuzzle.Tree
open Classical
open SlidingPuzzle.Hub
open Finset

variable {n k s q : ℕ} [NeZero n] (L : LaneSys k q)

/-- Cells of the region of `Q`. -/
noncomputable def regionSize (s : ℕ) (Q : Sq k) : ℕ :=
  #(univ.filter fun x : Cell n => region L s Q x)

/-- Total length of all lanes. -/
def laneCells (s : ℕ) : ℕ := (∑ H : LaneI k q, rowLen L s H) + ∑ V : LaneI k q, colLen L s V

theorem rowCell_nonblank (td : TDims n k s q) {B : Board n}
    (hb : reservoir k s (sqOf td.hd (blank B)) (blank B)) (H : LaneI k q) {p : ℕ}
    (hp : p < rowLen L s H) : (B (rowCell s H p)).val ≠ 0 := by
  refine val_ne_zero_of_ne_blank fun he => ?_
  have h1 := key_rowCell L td H p hp
  rw [he, key_reservoir L td hb] at h1
  cases h1

theorem colCell_nonblank (td : TDims n k s q) {B : Board n}
    (hb : reservoir k s (sqOf td.hd (blank B)) (blank B)) (V : LaneI k q) {p : ℕ}
    (hp : p < colLen L s V) : (B (colCell s V p)).val ≠ 0 := by
  refine val_ne_zero_of_ne_blank fun he => ?_
  have h1 := key_colCell L td V p hp
  rw [he, key_reservoir L td hb] at h1
  cases h1

/-- A board with its blank in a reservoir realizes its own abstraction. -/
theorem rel_absState (td : TDims n k s q) (B : Board n)
    (hb : reservoir k s (sqOf td.hd (blank B)) (blank B)) : Rel L td.hd B (absState L td.hd B) :=
  ⟨fun H _ hp => ⟨rowCell_nonblank L td hb H hp, rfl⟩,
    fun V _ hp => ⟨colCell_nonblank L td hb V hp, rfl⟩, fun _ _ => rfl, hb⟩

/-- Every region's tiles, and possibly the blank, fill it. -/
theorem absState_regionTotal (td : TDims n k s q) (B : Board n)
    (hb : reservoir k s (sqOf td.hd (blank B)) (blank B)) (Q : Sq k) :
    (∑ y, (absState L td.hd B).cnt Q y) + (if (absState L td.hd B).blank = Q then 1 else 0) =
      regionSize (n := n) L s Q := by
  show (∑ y, regionCount L td.hd B Q y) + (if sqOf td.hd (blank B) = Q then 1 else 0) = _
  have h1 : ∑ y, regionCount L td.hd B Q y =
      #(univ.filter fun x => region L s Q x ∧ (B x).val ≠ 0) := by
    rw [card_eq_sum_card_fiberwise (f := fun x => classOf td.hd (B x)) (t := univ)
      (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun y _ => ?_
    unfold regionCount
    rw [filter_filter]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    tauto
  have h2 := card_filter_add_card_filter_not (s := univ.filter fun x : Cell n => region L s Q x)
    (fun x => (B x).val ≠ 0)
  rw [filter_filter, filter_filter] at h2
  have h3 : #(univ.filter fun x => region L s Q x ∧ ¬ (B x).val ≠ 0) =
      if sqOf td.hd (blank B) = Q then 1 else 0 := by
    split_ifs with hQ
    · rw [card_eq_one]
      refine ⟨blank B, ?_⟩
      ext x
      simp only [mem_filter, mem_univ, true_and, not_not, mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        exact LayoutFacts.eq_blank_of_val_eq_zero h
      · rintro rfl
        refine ⟨region_of_reservoir L td (hQ ▸ hb), ?_⟩
        simp [blank, position]
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨hr, h⟩
      have hx := LayoutFacts.eq_blank_of_val_eq_zero (not_not.mp h)
      subst hx
      exact hQ (region_sqOf L td.hd hr)
  rw [h1, ← h3]
  exact h2

/-- Every class has `s²` tiles, the last one `s² - 1` besides the blank. -/
theorem absState_classTotal (td : TDims n k s q) (B : Board n)
    (hb : reservoir k s (sqOf td.hd (blank B)) (blank B)) (y : Sq k) :
    (∑ Q, (absState L td.hd B).cnt Q y) + (absState L td.hd B).corrCount L s y =
      s ^ 2 - (if IsLast y then 1 else 0) := by
  have hc := count_decomp L td (fun x => (B x).val ≠ 0 ∧ classOf td.hd (B x) = y)
  rw [LayoutFacts.card_class td.hd B y] at hc
  rw [← hc, add_assoc]
  congr 1
  unfold IState.corrCount
  congr 1
  · refine sum_congr rfl fun H _ => ?_
    congr 1
    refine filter_congr fun p hp => ?_
    have := rowCell_nonblank L td hb H (mem_range.mp hp)
    simp only [absState]
    tauto
  · refine sum_congr rfl fun V _ => ?_
    congr 1
    refine filter_congr fun p hp => ?_
    have := colCell_nonblank L td hb V (mem_range.mp hp)
    simp only [absState]
    tauto

/-- Misplaced tiles lie in lanes or are counted by `offCount`. -/
theorem misplaced_le_of_rel (td : TDims n k s q) {B : Board n} {σ : IState k q}
    (hR : Rel L td.hd B σ) : misplaced td.hd B ≤ laneCells L s + σ.offCount := by
  have hc := count_decomp L td (fun x => (B x).val ≠ 0 ∧ classOf td.hd (B x) ≠ sqOf td.hd x)
  have hm : misplaced td.hd B =
      #(univ.filter fun x => (B x).val ≠ 0 ∧ classOf td.hd (B x) ≠ sqOf td.hd x) := rfl
  have hreg : ∀ Q : Sq k,
      #(univ.filter fun x => region L s Q x ∧
        ((B x).val ≠ 0 ∧ classOf td.hd (B x) ≠ sqOf td.hd x)) =
        ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y := by
    intro Q
    rw [card_eq_sum_card_fiberwise (f := fun x => classOf td.hd (B x)) (t := univ)
      (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun y _ => ?_
    rw [filter_filter]
    split_ifs with hyQ
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨⟨hr, -, hne⟩, he⟩
      exact hne (he.trans (hyQ.trans (region_sqOf L td.hd hr).symm))
    · rw [← hR.2.2.1 Q y]
      unfold regionCount
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hr, h0, -⟩, he⟩
        exact ⟨hr, h0, he⟩
      · rintro ⟨hr, h0, he⟩
        refine ⟨⟨hr, h0, ?_⟩, he⟩
        rw [he, region_sqOf L td.hd hr]
        exact hyQ
  have hrow : (∑ H : LaneI k q, #((range (rowLen L s H)).filter fun p =>
      (B (rowCell s H p)).val ≠ 0 ∧ classOf td.hd (B (rowCell s H p)) ≠
        sqOf td.hd (rowCell s H p))) ≤ ∑ H : LaneI k q, rowLen L s H :=
    sum_le_sum fun H _ => (card_filter_le _ _).trans (card_range _).le
  have hcol : (∑ V : LaneI k q, #((range (colLen L s V)).filter fun p =>
      (B (colCell s V p)).val ≠ 0 ∧ classOf td.hd (B (colCell s V p)) ≠
        sqOf td.hd (colCell s V p))) ≤ ∑ V : LaneI k q, colLen L s V :=
    sum_le_sum fun V _ => (card_filter_le _ _).trans (card_range _).le
  simp only [hreg] at hc
  have hoff : σ.offCount = ∑ Q : Sq k, ∑ y : Sq k, if y = Q then 0 else σ.cnt Q y := rfl
  unfold laneCells
  omega

omit [NeZero n] in
/-- A region contains every cell of its square with both offsets at least `q`. -/
theorem regionSize_ge (td : TDims n k s q) (Q : Sq k) :
    (s - q) * (s - q) ≤ regionSize (n := n) L s Q := by
  have h := LayoutFacts.card_square (n := n) td.hd Q (fun i j => q ≤ i ∧ q ≤ j)
  have he : ((range s ×ˢ range s).filter fun p : ℕ × ℕ => q ≤ p.1 ∧ q ≤ p.2) =
      Ico q s ×ˢ Ico q s := by
    ext ⟨i, j⟩; simp only [mem_filter, mem_product, mem_range, mem_Ico]; omega
  rw [he, card_product, Nat.card_Ico] at h
  rw [← h]
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  refine ⟨hx.1, hx.2.1, ?_⟩
  rintro (⟨h1, -⟩ | ⟨-, h1, -⟩) <;> omega

/-- The lanes have at most `2 q s` cells in every square, `2 q k n` in all. -/
theorem laneCells_le (td : TDims n k s q) : laneCells L s ≤ k ^ 2 * (2 * q * s) := by
  have hc := count_decomp L td (fun _ : Cell n => True)
  have hn : #(univ : Finset (Cell n)) = k ^ 2 * s ^ 2 := by
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, ← td.mul]; ring
  have hU : (univ.filter fun _ : Cell n => True) = univ := by ext; simp
  rw [hU, hn] at hc
  simp only [and_true] at hc
  have hreg : ∀ Q : Sq k, (s - q) * (s - q) ≤ #(univ.filter fun x : Cell n => region L s Q x) :=
    regionSize_ge L td
  have hsum : ∑ _Q : Sq k, (s - q) * (s - q) ≤
      ∑ Q : Sq k, #(univ.filter fun x : Cell n => region L s Q x) := sum_le_sum fun Q _ => hreg Q
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at hsum
  have hrow : ∀ H : LaneI k q, #((range (rowLen L s H)).filter fun _ => True) = rowLen L s H := by
    intro H; simp
  have hcol : ∀ V : LaneI k q, #((range (colLen L s V)).filter fun _ => True) = colLen L s V := by
    intro V; simp
  simp only [hrow, hcol] at hc
  unfold laneCells
  have hqs := td.q_lt_s
  obtain ⟨m, hm⟩ : ∃ m, s = q + m := ⟨s - q, by omega⟩
  subst hm
  have e1 : q + m - q = m := by omega
  rw [e1] at hsum
  have e2 : k ^ 2 * (q + m) ^ 2 = k * k * (m * m) + k ^ 2 * (2 * q * (q + m)) - k ^ 2 * q ^ 2 := by
    have : k ^ 2 * (q + m) ^ 2 + k ^ 2 * q ^ 2 = k * k * (m * m) + k ^ 2 * (2 * q * (q + m)) := by
      ring
    omega
  have e3 : k ^ 2 * q ^ 2 ≤ k ^ 2 * (2 * q * (q + m)) := Nat.mul_le_mul_left _ (by nlinarith)
  omega

end SlidingPuzzle.Tree
