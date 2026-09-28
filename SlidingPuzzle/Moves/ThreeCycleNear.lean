import SlidingPuzzle.Moves.ThreeCycleSharp
import SlidingPuzzle.Moves.Local
import SlidingPuzzle.Parberry.PlacementDist

/-! # Three-cycles with two tiles near the corner

`exists_three_cycle_sharp` charges each of its three staging placements the
uniform budget `8n`. When two of the three tiles, and the blank, lie near the
top-left corner, their placements cost only `8` moves per unit of distance
(`Parberry.exists_placement_dist`), so staging costs `8n + O(δ)` and the
three-cycle `16n + O(δ)` (`exists_three_cycle_near`), where `δ` is the total
distance of the blank and the two near tiles from the corner. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin n))

/-- A path moves every tile at most its length. -/
theorem Path.gridDistance_position_le {B C : Board n} (p : Path B C) (t : Tile n) :
    gridDistance (position B t) (position C t) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons A A' D hstep p ih =>
      show _ ≤ p.length + 1
      obtain ⟨c, hc, rfl⟩ := hstep
      have h1 : gridDistance (position A t) (position (swapCells A (blank A) c) t) ≤ 1 := by
        rw [position_swapCells]
        by_cases e1 : position A t = blank A
        · rw [e1, Equiv.swap_apply_left]; omega
        by_cases e2 : position A t = c
        · rw [e2, Equiv.swap_apply_right, gridDistance_comm]; omega
        · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; simp
      have htri : gridDistance (position A t) (position D t) ≤
          gridDistance (position A t) (position (swapCells A (blank A) c) t) +
            gridDistance (position (swapCells A (blank A) c) t) (position D t) := by
        simp only [gridDistance, Nat.dist]; omega
      omega

omit [NeZero n] in
theorem gridDistance_triangle (x y z : Cell n) :
    gridDistance x z ≤ gridDistance x y + gridDistance y z := by
  simp only [gridDistance, Nat.dist]; omega

/-- Place tile `t` at `(0, b+1)` with the blank below `(0, b)`, keeping `(0, 0..b)`,
in at most `8` moves per unit of distance. -/
theorem exists_place_top_dist (D : Board n) (b : ℕ) (hb2 : b + 2 < n)
    (hblank : blank D = (⟨1, by omega⟩, ⟨b, by omega⟩)) (t : Tile n) (ht0 : t ≠ 0)
    (hfree : ∀ i (hi : i ≤ b), D (0, ⟨i, by omega⟩) ≠ t) :
    ∃ E : Board n, ∃ q : Path D E,
      q.length ≤ 8 * gridDistance (position D t) c(0, b + 1) + 1 ∧
      blank E = (⟨1, by omega⟩, ⟨b + 1, by omega⟩) ∧
      E (0, ⟨b + 1, by omega⟩) = t ∧
      ∀ i (hi : i ≤ b), E (0, ⟨i, by omega⟩) = D (0, ⟨i, by omega⟩) := by
  set s := D.symm t with hs
  have hDs : D s = t := D.apply_symm_apply t
  have hfree' : 0 < s.1.val ∨ (0 = s.1.val ∧ b + 1 ≤ s.2.val) := by
    by_contra hh
    have h1 : s.1 = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have h2 : s.2.val ≤ b := by omega
    apply hfree s.2.val h2
    rw [← hDs]
    congr 1
    exact Prod.ext h1.symm rfl
  have hne : (s.1, s.2) ≠ blank D := by
    intro he
    apply ht0
    rw [← hDs, show s = blank D from he]
    exact D.apply_symm_apply 0
  obtain ⟨E, q, hq, hbE, hE, hfix⟩ :=
    Parberry.exists_placement_dist D 0 b s.1 s.2 hfree' hne (by omega) hb2 hblank
  refine ⟨E, q, ?_, hbE, ?_, ?_⟩
  · have : position D t = (s.1, s.2) := rfl
    rw [this]; exact hq
  · have e : ((0 : Fin n), (⟨b + 1, by omega⟩ : Fin n)) =
        ((⟨0, by omega⟩ : Fin n), (⟨b + 1, by omega⟩ : Fin n)) := Prod.ext (Fin.ext (by simp)) rfl
    rw [e, hE]; exact hDs
  · intro i hi
    exact hfix _ (Or.inr ⟨rfl, by simp only; omega⟩)

/-- With the blank below the corner, four moves replace the corner tile by its
right neighbour and return the blank. -/
theorem exists_kick (B : Board n) (hn : 2 ≤ n) (hb : blank B = c(1, 0)) :
    ∃ C : Board n, ∃ p : Path B C, p.length = 4 ∧ blank C = c(1, 0) ∧
      C c(0, 0) = B c(0, 1) := by
  have d1 : gridDistance (blank B) c(0, 0) = 1 := by
    rw [hb]; simp [gridDistance, Nat.dist]
  let B1 := swapCells B (blank B) c(0, 0)
  have hb1 : blank B1 = c(0, 0) := blank_swapCells B _
  have d2 : gridDistance (blank B1) c(0, 1) = 1 := by
    rw [hb1]; simp [gridDistance, Nat.dist]
  let B2 := swapCells B1 (blank B1) c(0, 1)
  have hb2 : blank B2 = c(0, 1) := blank_swapCells B1 _
  have d3 : gridDistance (blank B2) c(1, 1) = 1 := by
    rw [hb2]; simp [gridDistance, Nat.dist]
  let B3 := swapCells B2 (blank B2) c(1, 1)
  have hb3 : blank B3 = c(1, 1) := blank_swapCells B2 _
  have d4 : gridDistance (blank B3) c(1, 0) = 1 := by
    rw [hb3]; simp [gridDistance, Nat.dist]
  let B4 := swapCells B3 (blank B3) c(1, 0)
  have hb4 : blank B4 = c(1, 0) := blank_swapCells B3 _
  refine ⟨B4, (((movePath B c(0, 0) d1).append (movePath B1 c(0, 1) d2)).append
    (movePath B2 c(1, 1) d3)).append (movePath B3 c(1, 0) d4),
    by simp only [Path.length_append]; rfl, hb4, ?_⟩
  have n1 : (c(0, 0) : Cell n) ≠ c(1, 1) := by simp [Prod.ext_iff]
  have n2 : (c(0, 0) : Cell n) ≠ c(1, 0) := by simp [Prod.ext_iff]
  have n3 : (c(0, 1) : Cell n) ≠ c(1, 0) := by simp [Prod.ext_iff]
  have e4 : B4 c(0, 0) = B3 c(0, 0) := by
    simp only [B4]; rw [hb3]; exact swapCells_preserves B3 n1 n2
  have e3 : B3 c(0, 0) = B2 c(0, 0) := by
    simp only [B3]; rw [hb2]
    exact swapCells_preserves B2 (by simp [Prod.ext_iff]) n1
  have e2 : B2 c(0, 0) = B1 c(0, 1) := by
    simp only [B2]; rw [hb1]; exact swapCells_at_left B1 _ _
  have e1 : B1 c(0, 1) = B c(0, 1) := by
    simp only [B1]; rw [hb]; exact swapCells_preserves B n3 (by simp [Prod.ext_iff])
  rw [e4, e3, e2, e1]

/-- Tiles move at most the path length, measured from a fixed cell. -/
theorem dist_after {B C : Board n} (p : Path B C) (t : Tile n) (e : Cell n) :
    gridDistance (position C t) e ≤ gridDistance (position B t) e + p.length := by
  have h1 := p.gridDistance_position_le t
  simp only [gridDistance, Nat.dist] at h1 ⊢
  omega

/-- Stage three tiles as in `exists_stage_three_sharp`, placing `x` and `z` by
distance and only `y` with the uniform budget. -/
theorem exists_stage_three_near (B : Board n) (hn : 6 ≤ n) (x y z : Tile n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ j, ∃ hj : j ≤ 1, ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8 * n + 81 * (gridDistance (blank B) c(1, 0) +
        gridDistance (position B x) c(0, 0) + gridDistance (position B z) c(0, 0)) + 424 ∧
      blank C = (⟨1, by omega⟩, ⟨j, by omega⟩) ∧
      ((C (0, ⟨j, by omega⟩) = x ∧ C (0, ⟨j + 1, by omega⟩) = y ∧
          C (0, ⟨j + 2, by omega⟩) = z) ∨
        (C (0, ⟨j, by omega⟩) = y ∧ C (0, ⟨j + 1, by omega⟩) = z ∧
          C (0, ⟨j + 2, by omega⟩) = x) ∨
        (C (0, ⟨j, by omega⟩) = z ∧ C (0, ⟨j + 1, by omega⟩) = x ∧
          C (0, ⟨j + 2, by omega⟩) = y)) := by
  set β := gridDistance (blank B) c(1, 0)
  set α := gridDistance (position B x) c(0, 0)
  set γ := gridDistance (position B z) c(0, 0)
  -- the blank below the corner, and `x` out of the corner
  have hD0 : ∃ D0 : Board n, ∃ p0 : Path B D0, p0.length ≤ β + 4 ∧
      blank D0 = c(1, 0) ∧ D0 (0, ⟨0, by omega⟩) ≠ x := by
    obtain ⟨D1, w1, hbD1, hw1, -⟩ := exists_blank_access_path_preserving B c(1, 0)
    by_cases hk : D1 (0, ⟨0, by omega⟩) = x
    · obtain ⟨D2, w2, hw2, hbD2, hD2⟩ := exists_kick D1 (by omega) hbD1
      refine ⟨D2, w1.append w2, by rw [Path.length_append]; omega, hbD2, ?_⟩
      have e : (0, (⟨0, by omega⟩ : Fin n)) = c(0, 0) := rfl
      rw [e, hD2, ← hk]
      intro h
      have := D1.injective h
      simp [Prod.ext_iff] at this
    · exact ⟨D1, w1, hw1.trans (Nat.le_add_right _ _), hbD1, hk⟩
  obtain ⟨D0, p0, hp0, hb0, hx0⟩ := hD0
  have hb0' : blank D0 = (⟨1, by omega⟩, ⟨0, by omega⟩) := hb0
  have dx0 := dist_after p0 x c(0, 0)
  have dz0 := dist_after p0 z c(0, 0)
  have hsh (u v : Cell n) : gridDistance u v ≤ gridDistance u c(0, 0) + gridDistance c(0, 0) v :=
    gridDistance_triangle u c(0, 0) v
  have hshift : ∀ (u : Cell n) (j : ℕ) (hj : j < n),
      gridDistance u ((⟨0, by omega⟩ : Fin n), (⟨j, hj⟩ : Fin n)) ≤ gridDistance u c(0, 0) + j := by
    intro u j hj; simp only [gridDistance, Nat.dist]; omega
  have g01 : gridDistance (c(0, 0) : Cell n) c(0, 1) = 1 := by simp [gridDistance, Nat.dist]
  have g02 : gridDistance (c(0, 0) : Cell n) c(0, 2) = 2 := by simp [gridDistance, Nat.dist]
  have g03 : gridDistance (c(0, 0) : Cell n) c(0, 3) = 3 := by simp [gridDistance, Nat.dist]
  -- placing `u` then `v` by distance at `(0,1), (0,2)`
  have two (u v : Tile n) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
      (hu0 : D0 (0, ⟨0, by omega⟩) ≠ u) (hv0 : D0 (0, ⟨0, by omega⟩) ≠ v) :
      ∃ E : Board n, ∃ q : Path D0 E,
        q.length ≤ 72 * gridDistance (position D0 u) c(0, 0) +
          8 * gridDistance (position D0 v) c(0, 0) + 98 ∧
        blank E = (⟨1, by omega⟩, ⟨2, by omega⟩) ∧
        E (0, ⟨0, by omega⟩) = D0 (0, ⟨0, by omega⟩) ∧
        E (0, ⟨1, by omega⟩) = u ∧ E (0, ⟨2, by omega⟩) = v := by
    obtain ⟨E1, q1, hq1, hb1, hE1, hf1⟩ := exists_place_top_dist D0 0 (by omega) hb0' u hu
      (fun i hi => by
        have : i = 0 := by omega
        subst this; exact hu0)
    obtain ⟨E2, q2, hq2, hb2, hE2, hf2⟩ := exists_place_top_dist E1 1 (by omega) hb1 v hv
      (fun i hi => by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
        · subst h; rw [hf1 0 le_rfl]; exact hv0
        · subst h; rw [hE1]; exact huv)
    have hu1 := hshift (position D0 u) (0 + 1) (by omega)
    have hv1 := dist_after q1 v c(0, 0)
    have hv2 := hshift (position E1 v) (1 + 1) (by omega)
    refine ⟨E2, q1.append q2, ?_, hb2, ?_, ?_, hE2⟩
    · rw [Path.length_append]
      omega
    · rw [hf2 0 (by omega), hf1 0 le_rfl]
    · rw [hf2 1 le_rfl]; exact hE1
  by_cases hcz : D0 (0, ⟨0, by omega⟩) = z
  · -- stage `z, x, y` at columns `0, 1, 2`
    obtain ⟨E1, q1, hq1, hb1, hE1, hf1⟩ := exists_place_top_dist D0 0 (by omega) hb0' x hx
      (fun i hi => by
        have : i = 0 := by omega
        subst this; exact hx0)
    obtain ⟨E2, q2, hq2, hb2, hE2, hf2⟩ := exists_place_top E1 1 (by omega) hb1 y hy
      (fun i hi => by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
        · subst h; rw [hf1 0 le_rfl, hcz]; exact hyz.symm
        · subst h; rw [hE1]; exact hxy)
    obtain ⟨E3, q3, hb3, hq3, hf3⟩ :=
      exists_blank_access_path_preserving E2 (⟨1, by omega⟩, ⟨0, by omega⟩)
    have hrow : ∀ i (hi : i < n), E3 (0, ⟨i, hi⟩) = E2 (0, ⟨i, hi⟩) := fun i hi =>
      hf3 _ (Or.inl (by rw [hb2]; simp))
    refine ⟨0, by omega, E3, (p0.append q1).append (q2.append q3), ?_, hb3,
      Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
    · have hd : gridDistance (blank E2) (⟨1, by omega⟩, ⟨0, by omega⟩) = 2 := by
        rw [hb2]; simp [gridDistance, Nat.dist]
      have hm2 : 2 ≤ min (1 + 1) (n - (1 + 1)) := by omega
      have hx1 := hshift (position D0 x) (0 + 1) (by omega)
      simp only [Path.length_append]
      omega
    · rw [hrow, hf2 0 (by omega), hf1 0 le_rfl, hcz]
    · rw [hrow, hf2 1 le_rfl, hE1]
    · rw [hrow, hE2]
  by_cases hcy : D0 (0, ⟨0, by omega⟩) = y
  · -- stage `y, z, x` at columns `0, 1, 2`
    obtain ⟨E2, q, hq, hb2, hE0, hE1, hE2⟩ := two z x hz hx hxz.symm
      (fun h => hyz (by rw [← hcy, h])) hx0
    obtain ⟨E3, q3, hb3, hq3, hf3⟩ :=
      exists_blank_access_path_preserving E2 (⟨1, by omega⟩, ⟨0, by omega⟩)
    have hrow : ∀ i (hi : i < n), E3 (0, ⟨i, hi⟩) = E2 (0, ⟨i, hi⟩) := fun i hi =>
      hf3 _ (Or.inl (by rw [hb2]; simp))
    refine ⟨0, by omega, E3, (p0.append q).append q3, ?_, hb3,
      Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
    · have hd : gridDistance (blank E2) (⟨1, by omega⟩, ⟨0, by omega⟩) = 2 := by
        rw [hb2]; simp [gridDistance, Nat.dist]
      simp only [Path.length_append]
      nlinarith
    · rw [hrow, hE0, hcy]
    · rw [hrow, hE1]
    · rw [hrow, hE2]
  · -- stage `z, x, y` at columns `1, 2, 3`
    obtain ⟨E2, q, hq, hb2, hE0, hE1, hE2⟩ := two z x hz hx hxz.symm hcz hx0
    obtain ⟨E3, q3, hq3, hb3, hE3, hf3⟩ := exists_place_top E2 2 (by omega) hb2 y hy
      (fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h | h | h
        · subst h; rw [hE0]; exact hcy
        · subst h; rw [hE1]; exact hyz.symm
        · subst h; rw [hE2]; exact hxy)
    obtain ⟨E4, q4, hb4, hq4, hf4⟩ :=
      exists_blank_access_path_preserving E3 (⟨1, by omega⟩, ⟨1, by omega⟩)
    have hrow : ∀ i (hi : i < n), E4 (0, ⟨i, hi⟩) = E3 (0, ⟨i, hi⟩) := fun i hi =>
      hf4 _ (Or.inl (by rw [hb3]; simp))
    refine ⟨1, le_rfl, E4, ((p0.append q).append q3).append q4, ?_, hb4,
      Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
    · have hd : gridDistance (blank E3) (⟨1, by omega⟩, ⟨1, by omega⟩) = 2 := by
        rw [hb3]; simp [gridDistance, Nat.dist]
      have hm3 : 3 ≤ min (2 + 1) (n - (2 + 1)) := by omega
      simp only [Path.length_append]
      nlinarith
    · rw [hrow, hf3 1 (by omega), hE1]
    · rw [hrow, hf3 2 le_rfl, hE2]
    · rw [hrow, hE3]

/-- Rotate three distinct nonblank tiles, `a` and `c` near the top-left corner,
restoring every other tile and the blank, in at most `16 n + 162 δ + 872` moves. -/
theorem exists_three_cycle_near (B : Board n) (hn : 6 ≤ n)
    (a b c : Cell n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : B a ≠ 0) (hb : B b ≠ 0) (hc : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 16 * n + 162 * (gridDistance (blank B) c(1, 0) + gridDistance a c(0, 0) +
        gridDistance c c(0, 0)) + 872 ∧ blank C = blank B ∧
      C a = B b ∧ C b = B c ∧ C c = B a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
  have hxy : B a ≠ B b := fun h => hab (B.injective h)
  have hxz : B a ≠ B c := fun h => hac (B.injective h)
  have hyz : B b ≠ B c := fun h => hbc (B.injective h)
  obtain ⟨j, hj, D, p, hp, hbD, hlay⟩ :=
    exists_stage_three_near B hn (B a) (B b) (B c) hxy hxz hyz ha hb hc
  obtain ⟨E, q, hq, hbE, hE0, hE1, hE2, hfixE⟩ :=
    exists_top_three_cycle_at D (by omega) j (by omega) hbD
  obtain ⟨F, r, hr, hbF, hF⟩ := p.exists_unstaged q hbE
  have hc0 : (0, (⟨j, by omega⟩ : Fin n)) ≠ (0, ⟨j + 1, by omega⟩) := by simp
  have hc1 : (0, (⟨j, by omega⟩ : Fin n)) ≠ (0, ⟨j + 2, by omega⟩) := by simp
  have hc2 : (0, (⟨j + 1, by omega⟩ : Fin n)) ≠ (0, ⟨j + 2, by omega⟩) := by simp
  have hsymm {w : Cell n} {t : Tile n} (h : D w = t) : D.symm t = w := by
    rw [← h]; exact D.symm_apply_apply w
  have hpa : position B (B a) = a := by simp [position]
  have hpc : position B (B c) = c := by simp [position]
  rw [hpa, hpc] at hp
  refine ⟨F, r, by omega, hbF, ?_, ?_, ?_, ?_⟩
  · rw [hF]
    rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [hsymm h0, hE0, h1]
    · rw [hsymm h2, hE2, h0]
    · rw [hsymm h1, hE1, h2]
  · rw [hF]
    rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [hsymm h1, hE1, h2]
    · rw [hsymm h0, hE0, h1]
    · rw [hsymm h2, hE2, h0]
  · rw [hF]
    rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [hsymm h2, hE2, h0]
    · rw [hsymm h1, hE1, h2]
    · rw [hsymm h0, hE0, h1]
  · intro w hwa hwb hwc
    rw [hF]
    have hne : ∀ t, t = B a ∨ t = B b ∨ t = B c → B w ≠ t := by
      rintro t (rfl | rfl | rfl) h
      · exact hwa (B.injective h)
      · exact hwb (B.injective h)
      · exact hwc (B.injective h)
    have hpos : ∀ i (hi : i < n), (0, ⟨i, hi⟩) = D.symm (B w) →
        D (0, ⟨i, hi⟩) = B w := fun i hi h => by rw [h]; exact D.apply_symm_apply _
    rw [hfixE]
    · exact D.apply_symm_apply _
    all_goals
      intro h
      have := hpos _ _ h.symm
      rcases hlay with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
      all_goals first
        | exact hne _ (Or.inl rfl) (by rw [← this]; assumption)
        | exact hne _ (Or.inr (Or.inl rfl)) (by rw [← this]; assumption)
        | exact hne _ (Or.inr (Or.inr rfl)) (by rw [← this]; assumption)

end SlidingPuzzle
