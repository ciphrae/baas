import SlidingPuzzle.Algorithm.PhaseStates
import SlidingPuzzle.Moves.Translation
import SlidingPuzzle.Algorithm.Preparation.Horizontal
import SlidingPuzzle.Moves.ColumnSchedule
import SlidingPuzzle.Algorithm.Preparation.Vertical

/-! Phase I (Preparation). Stage every group's corridor quota and one
representative per nonfinal group, spread the staged rows into the horizontal
corridors and the staged columns into the vertical corridors. The staging step
is abstract (`RepresentativeStaging`); `MixedStaging` supplies it. -/
namespace SlidingPuzzle
noncomputable section
open Classical
namespace Partition
section

theorem exists_staging_representative_row_path {n k : ℕ}
    (hk : Dims n k) [NeZero n] {L : ℕ} (hstaging : RepresentativeStaging hk L)
    (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ L+18*k^2*n ∧
      (∀ (i : GroupIndex k) (c : Cell n),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).1.val = n-1 ∧ (blank C).2.val = n-k^2 := by
  have hg := preparation_geometry hk
  have hk2 : 1 < k^2 := by nlinarith
  obtain ⟨A,p,hp,hstage,hrep,hbr,hbc⟩ := hstaging B
  let access : Cell n :=
    (⟨2*k^2+2,by omega⟩,⟨n-k^2,by omega⟩)
  obtain ⟨D,q,hblank,hq,hfix⟩ := exists_blank_access_path_preserving A access
  have hqstage (i : GroupIndex k) (c : Cell n) (hc : c ∈ stagingCells i) :
      D c = A c := by
    apply hfix
    rcases stagingCells_compressed hk hc with hr | hcol
    · left
      change c.1.val < min (blank A).1.val (2*k^2+2)
      exact lt_min (by omega) (by omega)
    · right; right; left
      change c.2.val < min (blank A).2.val (n-k^2)
      exact lt_min (by omega) (by omega)
  have hqrep (i : GroupIndex k) : D (representativeSource hk i) = A (representativeSource hk i) := by
    apply hfix
    left
    change 2*k^2 < min (blank A).1.val (2*k^2+2)
    exact lt_min (by omega) (by omega)
  obtain ⟨E,s,hs,hrow,hsfix,hsblank⟩ := exists_row_translation_with_blank D (2*k^2) (n-k^2)
    (k^2) (n-3-2*k^2) (by omega) (by omega) hk2 hblank
  have hEstage (i : GroupIndex k) (c : Cell n) (hc : c ∈ stagingCells i) :
      E c ∈ targetGroup i := by
    rw [hsfix c, hqstage i c hc]
    · exact hstage i c hc
    · rcases stagingCells_compressed hk hc with hr | hcol
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inl (by omega)))
  have hErep (i : GroupIndex k) (hi : i ≠ lastGroup k hk) :
      E (⟨n-3,by omega⟩,(representativeSource hk i).2) ∈ targetGroup i := by
    have hil : i.val < k^2 := by simp [pow_two]
    have hh := hrow ⟨i.val,hil⟩
    have hroweq : 2*k^2 + (n-3-2*k^2) = n-3 := by omega
    simp only [hroweq] at hh
    change E (⟨n-3,by omega⟩,(representativeSource hk i).2) =
      D (representativeSource hk i) at hh
    rw [hh,hqrep]
    exact hrep i hi
  refine ⟨E,(p.append q).append s,?_,hEstage,hErep,?_⟩
  · have hqbound : q.length ≤ 2*n := by
      apply hq.trans
      unfold gridDistance Nat.dist
      have := (blank A).1.isLt
      have := (blank A).2.isLt
      have := access.1.isLt
      have := access.2.isLt
      omega
    have hk2' := hk.two_le
    have hsbound : s.length ≤ 7*k^2*n := by
      calc
        s.length ≤ (n-3-2*k^2)*(6*k^2+3) := hs
        _ ≤ n*(7*k^2) := Nat.mul_le_mul (by omega) (by nlinarith)
        _ = 7*k^2*n := by ring
    have hkn : n ≤ k^2*n := Nat.le_mul_of_pos_left n (by positivity)
    simp only [Path.length_append]
    nlinarith
  · rw [hsblank]
    change 2*k^2+(n-3-2*k^2)+2 = n-1 ∧ n-k^2 = n-k^2
    omega

theorem exists_horizontal_prepared_path {n k : ℕ}
    (hk : Dims n k) [NeZero n] {L : ℕ} (hstaging : RepresentativeStaging hk L)
    (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ L+18*k^2*n+48*k^2*n^2 ∧ (blank C).1.val = n-1 ∧
      (∀ (i : GroupIndex k) (c : Cell n), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell n), c ∈ stagingC j i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk → C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).2.val = n-k^2 := by
  obtain ⟨A,p,hp,hstage,hrep,hbr,hbc⟩ := exists_staging_representative_row_path hk hstaging B
  obtain ⟨C,q,hq,hb,hH,hCs,hR⟩ := exists_horizontal_preparation_path hk A hstage hbr
  refine ⟨C,p.append q,?_,by rw [hb]; exact hbr,hH,?_,?_,by rw [hb]; exact hbc⟩
  · rw [Path.length_append]
    nlinarith
  · intro j i c hc
    rw [hCs j i c hc]
    exact hstage i c ((mem_stagingCells i c).mpr (Or.inr (Or.inr ⟨j,hc⟩)))
  · intro i hi
    rw [hR]
    exact hrep i hi

/-- Column `i` of a band needs only `i/k²` chunks; pairing `i` with `k³-1-i`
bounds the total number of chunks by `k³(k-1)/2`. -/
theorem sum_div_sq_le {k : ℕ} (hk : 2 ≤ k) :
    2*(∑ i ∈ Finset.range (k^3), i/k^2)+k^3 ≤ k^4 := by
  have hk2 : 0 < k^2 := by positivity
  have hrefl := Finset.sum_range_reflect (fun i => i/k^2) (k^3)
  have hpair : ∑ i ∈ Finset.range (k^3), (i/k^2+(k^3-1-i)/k^2) ≤
      ∑ _i ∈ Finset.range (k^3), (k-1) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    calc
      i/k^2+(k^3-1-i)/k^2 ≤ (i+(k^3-1-i))/k^2 := Nat.div_add_div_le_add_div
      _ = (k^3-1)/k^2 := by congr 1; omega
      _ ≤ k-1 := by
        apply Nat.le_sub_one_of_lt
        apply (Nat.div_lt_iff_lt_mul hk2).mpr
        have : k*k^2 = k^3 := by ring
        omega
  rw [Finset.sum_add_distrib, hrefl, Finset.sum_const, Finset.card_range, smul_eq_mul] at hpair
  have hk3 : k^3*(k-1)+k^3 = k^4 := by
    have h := Nat.sub_add_cancel (by omega : 1 ≤ k)
    calc
      k^3*(k-1)+k^3 = k^3*(k-1+1) := by ring
      _ = k^4 := by rw [h]; ring
  omega

theorem exists_vertical_band_path {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (a : ℕ) (ha : a < k)
    (hb : (blank B).2.val = n-k^2) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ k^4*(8*side n k^2+4*n+8*side n k) ∧ blank C = blank B ∧
      (∀ (r : Fin n) (c : Fin (k^3)),
        a*side n k+2*k ≤ r.val → r.val < (a+1)*side n k →
        C (r,⟨verticalDestination (side n k) k c.val,by
          have := verticalDestination_bounds hk c.val c.isLt; omega⟩) =
        B (r,⟨c.val,by have := vertical_geometry hk; have := c.isLt; omega⟩)) ∧
      (∀ x : Cell n, ¬ verticalPreparationBand k a x ∨ n-k^2 ≤ x.2.val → C x = B x) := by
  have hg := vertical_geometry hk
  have hk2 := hk.two_le
  have h2k : 2*k+2 ≤ side n k := by have := hk.sq_add_le; nlinarith
  have hblock : (a+1)*side n k ≤ n := hk.block_le ⟨a, ha⟩
  have hrows : a*side n k+2*k+(side n k-2*k) = (a+1)*side n k := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  obtain ⟨C,p,hp,hbC,hcol,hfix⟩ := exists_descending_column_schedule_var B (a*side n k+2*k)
    (side n k-2*k) (k^3) (side n k) (fun i => i/k^2) (by omega) (by omega) (by omega)
    (verticalDestination (side n k) k) (verticalDestination_strictMono hk2 (by omega)) (by
      intro i hi
      have hh := verticalDestination_bounds hk i hi
      rw [hb]
      refine ⟨hh.1,hh.2.2,hh.2.1,?_⟩
      have hid := Nat.div_add_mod' i (k^2)
      have hmul := Nat.mul_le_mul_left (i/k^2) (show k^2 ≤ side n k by omega)
      unfold verticalDestination
      omega)
  refine ⟨C,p,?_,hbC,?_,?_⟩
  · have hsum := sum_div_sq_le hk2
    set t := ∑ i ∈ Finset.range (k^3), i/k^2
    have hW : 4*n+side n k*(2*side n k+6*(side n k-2*k)+8) ≤ 8*side n k^2+4*n+8*side n k := by
      have h1 : 2*side n k+6*(side n k-2*k)+8 ≤ 8*side n k+8 := by omega
      have h2 := Nat.mul_le_mul_left (side n k) h1
      have h3 : side n k*(8*side n k+8) = 8*side n k^2+8*side n k := by ring
      omega
    have hlen : p.length ≤ t*(8*side n k^2+4*n+8*side n k) :=
      hp.trans (Nat.mul_le_mul_left t hW)
    have hmul := Nat.mul_le_mul_right (8*side n k^2+4*n+8*side n k) (show 2*t ≤ k^4 by omega)
    nlinarith
  · intro r c hrlo hrhi
    let j : Fin (side n k-2*k) := ⟨r.val-(a*side n k+2*k),by omega⟩
    have hh := hcol c.val c.isLt j
    have he : (⟨a*side n k+2*k+j.val,by omega⟩ : Fin n) = r := by
      apply Fin.ext
      change a*side n k+2*k+(r.val-(a*side n k+2*k)) = r.val
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

theorem exists_vertical_spread_prefix {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (R : ℕ) (hR : R ≤ k)
    (hb : (blank B).2.val = n-k^2) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ R*(k^4*(8*side n k^2+4*n+8*side n k)) ∧ blank C = blank B ∧
      (∀ (a : ℕ) (ha : a < R) (r : Fin n) (c : Fin (k^3)),
        a*side n k+2*k ≤ r.val → r.val < (a+1)*side n k →
        C (r,⟨verticalDestination (side n k) k c.val,by
          have := verticalDestination_bounds hk c.val c.isLt; omega⟩) =
        B (r,⟨c.val,by have := vertical_geometry hk; have := c.isLt; omega⟩)) ∧
      (∀ x : Cell n, (∀ a < R, ¬ verticalPreparationBand k a x) ∨
        n-k^2 ≤ x.2.val → C x = B x) := by
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
      have : (R+1)*(k^4*(8*side n k^2+4*n+8*side n k)) = R*(k^4*(8*side n k^2+4*n+8*side n k))+k^4*(8*side n k^2+4*n+8*side n k) := by ring
      omega
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

theorem exists_vertical_preparation_path {n k : ℕ} (hk : Dims n k) [NeZero n]
    (B : Board n) (hb : (blank B).2.val = n-k^2)
    (hH : ∀ (i : GroupIndex k) (c : Cell n), horizontal i c → B c ∈ targetGroup i)
    (hV : ∀ (j i : GroupIndex k) (c : Cell n), c ∈ stagingC j i → B c ∈ targetGroup i) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ k^5*(8*side n k^2+4*n+8*side n k) ∧ Clear (k := k) C ∧
      (∀ i : GroupIndex k, C (representativeDestination hk i) = B (representativeDestination hk i)) := by
  have hg := vertical_geometry hk
  obtain ⟨C,p,hp,hbC,hcols,hfix⟩ := exists_vertical_spread_prefix hk B k le_rfl hb
  refine ⟨C,p,?_,⟨?_,?_⟩,?_⟩
  · calc
      2*p.length ≤ k*(k^4*(8*side n k^2+4*n+8*side n k)) := hp
      _ = k^5*(8*side n k^2+4*n+8*side n k) := by ring
  · intro i c hc
    rw [hfix c (Or.inl (by
      intro a ha hh
      have hmod := horizontal_mod hk hc
      have hdiv : c.1.val/side n k = a := Nat.div_eq_of_lt_le (by have := hh.1; omega) hh.2
      have he := Nat.div_add_mod' c.1.val (side n k)
      rw [hdiv] at he
      have := hh.1
      omega))]
    exact hH i c hc
  · intro j i c hc
    have hi : i.val < k^2 := by simp [pow_two]
    have hcol := (groupCol j).isLt
    have hsource : (groupCol j).val*k^2+i.val < k^3 := by
      have hh := Nat.mul_le_mul_right (k^2) hcol
      have he : k*k^2 = k^3 := by ring
      nlinarith
    let s : Fin (k^3) := ⟨(groupCol j).val*k^2+i.val,hsource⟩
    have hd : verticalDestination (side n k) k s.val = (groupCol j).val*side n k+i.val := by
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
    have he : (⟨verticalDestination (side n k) k s.val,by
        have := verticalDestination_bounds hk s.val s.isLt; omega⟩ : Fin n) = c.2 :=
      Fin.ext (hd.trans hc.2.2.symm)
    rw [he] at hh
    rw [hh]
    apply hV j i
    exact (mem_stagingC j i _).mpr ⟨hc.1,hc.2.1,rfl⟩
  · intro i
    apply hfix
    right
    change n-k^2 ≤ n-k^2+i.val
    omega

theorem exists_preparation_path {n k : ℕ}
    (hk : Dims n k) [NeZero n] {L : ℕ} (hstaging : RepresentativeStaging hk L)
    (B : Board n) :
    ∃ C : Board n, ∃ p : Path B C,
      2*p.length ≤ L+18*k^2*n+48*k^2*n^2+k^5*(8*side n k^2+4*n+8*side n k) ∧ Clear (k := k) C ∧ LastRepresentatives hk C := by
  classical
  obtain ⟨A,p,hp,_,hH,hV,hR,hb⟩ := exists_horizontal_prepared_path hk hstaging B
  obtain ⟨C,q,hq,hclear,hfix⟩ := exists_vertical_preparation_path hk A hb hH hV
  refine ⟨C,p.append q,?_,hclear,?_⟩
  · rw [Path.length_append]
    nlinarith
  · intro i hi
    have hc : representativeDestination hk i ∈ reservoirCells (lastGroup k hk) := by
      simpa only [mem_reservoirCells] using representative_destination_in_last_reservoir hk i
    have hmem : C (representativeDestination hk i) ∈ targetGroup i := by
      rw [hfix]
      exact hR i hi
    unfold reservoirCount
    have hh := Finset.single_le_sum (f := fun x : Cell n =>
      if C x ∈ targetGroup i then 1 else 0) (fun _ _ => Nat.zero_le _) hc
    rw [if_pos hmem] at hh
    omega

end
end Partition
end
end SlidingPuzzle
