import Zhong.Algorithm.Assembly
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Moves.BlankAccess

/-! Place a short top-row prefix with cost proportional to its length. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Place only the requested prefix, rather than paying for an entire row. -/
theorem exists_top_prefix_path (B : Board n) (hn : 4 ≤ n) (d : ℕ) (hd : d ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ 502*d*n ∧
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
        p.length + q.length ≤ 502*d*n + 251*(n+n) := Nat.add_le_add hp (hq.trans hlen)
        _ = 502*(d+1)*n := by ring
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
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ 502*d*n ∧
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
  have hq : ∃ q : Path B (relabel D e.symm), q.length ≤ 502*d*n := by
    have h : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
        q.length ≤ 502*d*n := ⟨p.relabel e.symm hes, by simpa using hp⟩
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
end SlidingPuzzle
