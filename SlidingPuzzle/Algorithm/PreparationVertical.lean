import SlidingPuzzle.Algorithm.PreparationHorizontal
import SlidingPuzzle.Moves.ColumnSchedule

/-! Preparation step (iii): spread vertical quotas while preserving horizontal
corridors and the explicit representative row. -/
namespace SlidingPuzzle.Partition
noncomputable section

/-- Destination of a compressed column in a vertical data band. -/
def verticalDestination (k i : ℕ) : ℕ := i/k^2*k^3+i%k^2

/-- The data rows in the `a`-th block row, excluding horizontal corridors. -/
def verticalPreparationBand {n : ℕ} (k a : ℕ) (c : Cell n) : Prop :=
  a*k^3+k ≤ c.1.val ∧ c.1.val < (a+1)*k^3

theorem vertical_geometry {k : ℕ} (hk : 2 ≤ k) :
    4 ≤ k^2 ∧ 2*k^2 ≤ k^3 ∧ k+2 ≤ k^3 ∧ k^3 ≤ k^4 := by
  have hsq : 4 ≤ k^2 := by nlinarith
  have hksq : k ≤ k^2 := by nlinarith
  have htwo : 2*k^2 ≤ k^3 := by
    calc
      2*k^2 ≤ k*k^2 := Nat.mul_le_mul_right _ hk
      _ = k^3 := by ring
  have hfour : k^3 ≤ k^4 := by
    calc
      k^3 ≤ k*k^3 := Nat.le_mul_of_pos_left _ (by omega)
      _ = k^4 := by ring
  omega

theorem verticalDestination_strictMono {k : ℕ} (hk : 2 ≤ k) :
    StrictMono (verticalDestination k) := by
  intro i j hij
  have hg := vertical_geometry hk
  have hi := Nat.mod_lt i (by positivity : 0 < k^2)
  have hj := Nat.mod_lt j (by positivity : 0 < k^2)
  have hid := Nat.div_add_mod' i (k^2)
  have hjd := Nat.div_add_mod' j (k^2)
  have hdiv : i/k^2 ≤ j/k^2 := Nat.div_le_div_right hij.le
  by_cases he : i/k^2 = j/k^2
  · unfold verticalDestination
    rw [he] at hid ⊢
    omega
  · have hdiv' : i/k^2+1 ≤ j/k^2 := by omega
    calc
      verticalDestination k i < i/k^2*k^3+k^3 := by unfold verticalDestination; omega
      _ = (i/k^2+1)*k^3 := by ring
      _ ≤ j/k^2*k^3 := Nat.mul_le_mul_right _ hdiv'
      _ ≤ verticalDestination k j := Nat.le_add_right _ _

theorem verticalDestination_bounds {k : ℕ} (hk : 2 ≤ k)
    (i : ℕ) (hi : i < k^3) :
    i ≤ verticalDestination k i ∧ verticalDestination k i < k^4-k^2 ∧
      verticalDestination k i+3 ≤ k^4 := by
  have hg := vertical_geometry hk
  have hid := Nat.div_add_mod' i (k^2)
  have himod := Nat.mod_lt i (by positivity : 0 < k^2)
  have hidiv : i/k^2 < k := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [show k*k^2 = k^3 by ring] using hi
  have hmul := Nat.mul_le_mul_left (i/k^2) (show k^2 ≤ k^3 by omega)
  have hblock : i/k^2*k^3+k^3 ≤ k^4 := by
    calc
      i/k^2*k^3+k^3 = (i/k^2+1)*k^3 := by ring
      _ ≤ k*k^3 := Nat.mul_le_mul_right _ hidiv
      _ = k^4 := by ring
  unfold verticalDestination
  omega

theorem verticalPreparationBand_unique {n k a b : ℕ} {c : Cell n}
    (ha : verticalPreparationBand k a c) (hb : verticalPreparationBand k b c) : a = b := by
  have hda : c.1.val/k^3 = a := Nat.div_eq_of_lt_le (by have := ha.1; omega) ha.2
  have hdb : c.1.val/k^3 = b := Nat.div_eq_of_lt_le (by have := hb.1; omega) hb.2
  exact hda.symm.trans hdb

/-- Spread one row band's columns. Chunked access gives `14*k¹⁰` moves for
all `k³` columns, rather than paying board-wide access for every unit shift. -/
theorem exists_vertical_band_path {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (a : ℕ) (ha : a < k)
    (hb : (blank B).2.val = k^4-k^2) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 14*k^10 ∧ blank C = blank B ∧
      (∀ (r : Fin (k^4)) (c : Fin (k^3)),
        a*k^3+k ≤ r.val → r.val < (a+1)*k^3 →
        C (r,⟨verticalDestination k c.val,by have := verticalDestination_bounds hk c.val c.isLt; omega⟩) =
        B (r,⟨c.val,by have := vertical_geometry hk; have := c.isLt; omega⟩)) ∧
      (∀ x : Cell (k^4), ¬ verticalPreparationBand k a x ∨ k^4-k^2 ≤ x.2.val → C x = B x) := by
  have hg := vertical_geometry hk
  have hblock : (a+1)*k^3 ≤ k^4 := by
    calc
      (a+1)*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ ha
      _ = k^4 := by ring
  have hrows : a*k^3+k+(k^3-k) = (a+1)*k^3 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  obtain ⟨C,p,hp,hbC,hcol,hfix⟩ := exists_descending_column_schedule B (a*k^3+k)
    (k^3-k) (k^3) (k^3) k (by omega) (by omega) (by omega)
    (verticalDestination k) (verticalDestination_strictMono hk) (by
      intro i hi
      have hh := verticalDestination_bounds hk i hi
      rw [hb]
      refine ⟨hh.1,hh.2.2,hh.2.1,?_⟩
      rw [show k*k^3 = k^4 by ring]
      omega)
  refine ⟨C,p,?_,hbC,?_,?_⟩
  · have hinner : 2*k^3+6*(k^3-k)+8 ≤ 10*k^3 := by omega
    have h46 : k^4 ≤ k^6 := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      p.length ≤ k^3*(k*(4*k^4+k^3*(2*k^3+6*(k^3-k)+8))) := hp
      _ ≤ k^3*(k*(4*k^6+k^3*(10*k^3))) := by gcongr
      _ = 14*k^10 := by ring
  · intro r c hrlo hrhi
    let j : Fin (k^3-k) := ⟨r.val-(a*k^3+k),by omega⟩
    have hh := hcol c.val c.isLt j
    have he : (⟨a*k^3+k+j.val,by omega⟩ : Fin (k^4)) = r := by
      apply Fin.ext
      change a*k^3+k+(r.val-(a*k^3+k)) = r.val
      omega
    simpa only [he] using hh
  · intro x hx
    apply hfix
    rcases hx with hx | hx
    · unfold verticalPreparationBand at hx
      omega
    · right; right
      intro i hi
      have hh := verticalDestination_bounds hk i hi
      omega

/-- Execute the independent row-band schedules, retaining their exact effects
relative to the original board and restoring every cell outside their support. -/
theorem exists_vertical_spread_prefix {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (R : ℕ) (hR : R ≤ k)
    (hb : (blank B).2.val = k^4-k^2) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 14*R*k^10 ∧ blank C = blank B ∧
      (∀ (a : ℕ) (ha : a < R) (r : Fin (k^4)) (c : Fin (k^3)),
        a*k^3+k ≤ r.val → r.val < (a+1)*k^3 →
        C (r,⟨verticalDestination k c.val,by have := verticalDestination_bounds hk c.val c.isLt; omega⟩) =
        B (r,⟨c.val,by have := vertical_geometry hk; have := c.isLt; omega⟩)) ∧
      (∀ x : Cell (k^4), (∀ a < R, ¬ verticalPreparationBand k a x) ∨
        k^4-k^2 ≤ x.2.val → C x = B x) := by
  induction R with
  | zero =>
    refine ⟨B,Path.nil B,by simp,rfl,?_,fun _ _ => rfl⟩
    intro a ha
    omega
  | succ R ih =>
    obtain ⟨D,p,hp,hbD,hcolsD,hfixD⟩ := ih (by omega)
    obtain ⟨E,q,hq,hbE,hcolsE,hfixE⟩ := exists_vertical_band_path hk D R (by omega) (by rw [hbD]; exact hb)
    refine ⟨E,p.append q,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length+q.length ≤ 14*R*k^10+14*k^10 := Nat.add_le_add hp hq
        _ = 14*(R+1)*k^10 := by ring
    · intro a ha r c hrlo hrhi
      by_cases har : a < R
      · rw [hfixE _ (Or.inl (by
          intro hh
          have he := verticalPreparationBand_unique (show verticalPreparationBand k a _ from ⟨hrlo,hrhi⟩) hh
          omega))]
        exact hcolsD a har r c hrlo hrhi
      · have he : a = R := by omega
        subst a
        rw [hcolsE r c hrlo hrhi]
        apply hfixD
        left
        intro a ha hh
        have he := verticalPreparationBand_unique hh (show verticalPreparationBand k R _ from ⟨hrlo,hrhi⟩)
        omega
    · intro x hx
      rw [hfixE x (by
        rcases hx with hx | hx
        · exact Or.inl (hx R (by omega))
        · exact Or.inr hx)]
      apply hfixD
      rcases hx with hx | hx
      · exact Or.inl (fun a ha => hx a (by omega))
      · exact Or.inr hx

/-- Finish the vertical part of preparation from filled horizontal corridors and
compressed vertical quotas; all explicit reservoir representatives are preserved. -/
theorem exists_vertical_preparation_path {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hb : (blank B).2.val = k^4-k^2)
    (hH : ∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → B c ∈ targetGroup i)
    (hV : ∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → B c ∈ targetGroup i) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 14*k^11 ∧ Clear (k := k) C ∧
      (∀ i : GroupIndex k, C (representativeDestination hk i) = B (representativeDestination hk i)) := by
  have hg := vertical_geometry hk
  obtain ⟨C,p,hp,hbC,hcols,hfix⟩ := exists_vertical_spread_prefix hk B k le_rfl hb
  refine ⟨C,p,?_,⟨?_,?_⟩,?_⟩
  · calc
      p.length ≤ 14*k*k^10 := hp
      _ = 14*k^11 := by ring
  · intro i c hc
    rw [hfix c (Or.inl (by
      intro a ha hh
      have hmod := horizontal_mod hk hc
      have hdiv : c.1.val/k^3 = a := Nat.div_eq_of_lt_le (by have := hh.1; omega) hh.2
      have he := Nat.div_add_mod' c.1.val (k^3)
      rw [hdiv] at he
      have := hh.1
      omega))]
    exact hH i c hc
  · intro j i c hc
    have hi : i.val < k^2 := by simpa [pow_two] using i.isLt
    have hcol := (groupCol j).isLt
    have hsource : (groupCol j).val*k^2+i.val < k^3 := by
      have hh := Nat.mul_le_mul_right (k^2) hcol
      have he : k*k^2 = k^3 := by ring
      nlinarith
    let s : Fin (k^3) := ⟨(groupCol j).val*k^2+i.val,hsource⟩
    have hd : verticalDestination k s.val = (groupCol j).val*k^3+i.val := by
      unfold verticalDestination
      dsimp [s]
      have hdiv : ((groupCol j).val*k^2+i.val)/k^2 = (groupCol j).val := by
        apply Nat.div_eq_of_lt_le
        · omega
        · rw [Nat.add_mul, Nat.one_mul]
          omega
      rw [hdiv]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
    have hh := hcols (groupRow j).val (groupRow j).isLt c.1 s hc.1 hc.2.1
    have he : (⟨verticalDestination k s.val,by have := verticalDestination_bounds hk s.val s.isLt; omega⟩ : Fin (k^4)) = c.2 :=
      Fin.ext (hd.trans hc.2.2.symm)
    rw [he] at hh
    rw [hh]
    apply hV j i
    exact (mem_stagingC j i _).mpr ⟨hc.1,hc.2.1,rfl⟩
  · intro i
    apply hfix
    right
    change k^4-k^2 ≤ k^4-k^2+i.val
    omega

end
end SlidingPuzzle.Partition
