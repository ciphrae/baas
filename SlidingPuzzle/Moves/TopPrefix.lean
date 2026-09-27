import Zhong.Algorithm.Assembly
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Moves.BlankAccess
import SlidingPuzzle.Parberry.RowPrefix

/-! Place a short top-row prefix with cost proportional to its length. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Place only the requested prefix, rather than paying for an entire row. -/
theorem exists_top_prefix_path (B : Board n) (hn : 4 ≤ n) (d : ℕ) (hd : d ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ (106*n+12)*d ∧
      ∀ j : Fin n, j.val < d → C (0,j) = target n (0,j) := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  induction d with
  | zero => exact ⟨B, Path.nil B, by simp, fun _ h => by omega⟩
  | succ d ih =>
    obtain ⟨C,p,hp,hC⟩ := ih (by omega)
    obtain ⟨σ,hat,_,_,hleft,hlen⟩ := Zhong.placeStep 0 (by omega) (by omega)
      hn 0 (by omega) C d (by omega) (by intros; omega) (by intros; omega)
      hC (by omega)
    obtain ⟨q,hq⟩ := path_of_zhong_word C σ
    refine ⟨Zhong.actSeq C σ,p.append q,?_,?_⟩
    · rw [Path.length_append]
      calc
        p.length + q.length ≤ (106*n+12)*d + (106*n+12) := Nat.add_le_add hp (by omega)
        _ = (106*n+12)*(d+1) := by ring
    · intro j hj
      by_cases h : j.val < d
      · exact hleft j h
      · have he : j = (⟨d,by omega⟩ : Fin n) := Fin.ext (by simp only; omega)
        rw [he]
        exact hat

/-- The short-prefix placement theorem allows arbitrary prescribed nonblank
labels by choosing a target board with its blank in the standard position. -/
theorem exists_top_prefix_path_relabel (B T : Board n) (hn : 4 ≤ n)
    (hblank : blank T = blank (target n)) (d : ℕ) (hd : d ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ (106*n+12)*d ∧
      ∀ j : Fin n, j.val < d → C (0,j) = T (0,j) := by
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e 0 = 0 := by
    change target n (blank T) = 0
    rw [hblank]
    simp [blank, position]
  have hes : e.symm 0 = 0 := by
    apply e.injective
    simp [he]
  obtain ⟨D,p,hp,hD⟩ := exists_top_prefix_path (relabel B e) hn d hd
  have hq : ∃ q : Path B (relabel D e.symm), q.length ≤ (106*n+12)*d := by
    have h : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
        q.length ≤ (106*n+12)*d := ⟨p.relabel e.symm hes, by simpa using hp⟩
    rwa [relabel_relabel_symm] at h
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm,q,hq,?_⟩
  intro j hj
  change e.symm (D (0,j)) = T (0,j)
  rw [hD j hj]
  simp [e]

/-- Move the blank below a nonblank top-row prefix without changing that prefix. -/
theorem exists_blank_below_top_prefix (B : Board n) (hn : 2 ≤ n) (d : ℕ)
    (hprefix : ∀ j : Fin n, j.val < d → B (0,j) ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 2*n ∧ blank C = (⟨1,by omega⟩,0) ∧
      ∀ j : Fin n, j.val < d → C (0,j) = B (0,j) := by
  let a : Cell n := (⟨1,by omega⟩,0)
  by_cases hb : (blank B).1.val = 0
  · have hc : d ≤ (blank B).2.val := by
      by_contra h
      have hh := hprefix (blank B).2 (by omega)
      have he : (blank B).1 = 0 := Fin.ext hb
      apply hh
      have hz : B (blank B) = 0 := B.apply_symm_apply 0
      have hc : (0,(blank B).2) = blank B := Prod.ext he.symm rfl
      rwa [hc]
    obtain ⟨C,p,hbC,hp,hfix⟩ := exists_blank_access_path_elbow B a
    refine ⟨C,p,hp,hbC,?_⟩
    intro j hj
    apply hfix
    · intro he; have := congrArg Fin.val he; simp only at this; omega
    · intro he; have := congrArg Fin.val he; change 0 = 1 at this; omega
  · obtain ⟨C,p,hbC,hp,hfix⟩ := exists_blank_access_path_preserving B a
    refine ⟨C,p,?_,hbC,?_⟩
    · apply hp.trans
      unfold gridDistance Nat.dist
      dsimp [a]
      have := (blank B).1.isLt
      have := (blank B).2.isLt
      omega
    · intro j _
      apply hfix
      left
      change 0 < min (blank B).1.val 1
      omega

/-- Stage three prescribed top-row positions using the sharp interior placements
for the second and third tiles. Only the first tile needs the boundary routine. -/
theorem exists_top_three_prefix_path (B : Board n) (hn : 4 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, p.length + 8 ≤ 124*n ∧
      ∀ j : Fin n, j.val < 3 → C (0,j) = target n (0,j) := by
  obtain ⟨D,p,hp,hD⟩ := exists_top_prefix_path B hn 1 (by omega)
  have hnonzero (j : Fin n) (hj : j.val < 1) : D (0,j) ≠ 0 := by
    rw [hD j hj]
    exact Zhong.target_ne_zero 0 j.val j.isLt (by omega)
  obtain ⟨E,q,hq,hbE,hE⟩ := exists_blank_below_top_prefix D (by omega) 1 hnonzero
  have hfixed : ∀ z : Cell n, z.1.val < 0 ∨ (z.1.val = 0 ∧ z.2.val < 1) →
      E z = target n z := by
    intro z hz
    simp only [Nat.not_lt_zero, false_or] at hz
    have hz0 : z.1 = 0 := Fin.ext (by simpa using hz.1)
    rcases z with ⟨x,y⟩
    dsimp at hz0
    subst x
    exact (hE y hz.2).trans (hD y hz.2)
  obtain ⟨F,r,hr,hbF,hF⟩ := Parberry.exists_row_prefix E 0 2 (by omega) (by omega) hbE hfixed
  refine ⟨F,(p.append q).append r,?_,?_⟩
  · have hr' : r.length + 20 ≤ 16*n := by
      have hbudget : Parberry.rowPrefixBudget n 2 + 20 ≤ 16*n := by
        simp [Parberry.rowPrefixBudget, Finset.sum_range_succ, Parberry.rowStepBudget]
        omega
      omega
    simp only [Path.length_append]
    omega
  · intro j hj
    exact hF (0,j) (by simp; omega)

/-- Relabeled form of the sharp three-tile staging prefix. -/
theorem exists_top_three_prefix_path_relabel (B T : Board n) (hn : 4 ≤ n)
    (hblank : blank T = blank (target n)) :
    ∃ C : Board n, ∃ p : Path B C, p.length + 8 ≤ 124*n ∧
      ∀ j : Fin n, j.val < 3 → C (0,j) = T (0,j) := by
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e 0 = 0 := by
    change target n (blank T) = 0
    rw [hblank]
    simp [blank, position]
  have hes : e.symm 0 = 0 := by
    apply e.injective
    simp [he]
  obtain ⟨D,p,hp,hD⟩ := exists_top_three_prefix_path (relabel B e) hn
  have hq : ∃ q : Path B (relabel D e.symm), q.length + 8 ≤ 124*n := by
    have h : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
        q.length + 8 ≤ 124*n := ⟨p.relabel e.symm hes, by simpa using hp⟩
    rwa [relabel_relabel_symm] at h
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm,q,hq,?_⟩
  intro j hj
  change e.symm (D (0,j)) = T (0,j)
  rw [hD j hj]
  simp [e]

end SlidingPuzzle
