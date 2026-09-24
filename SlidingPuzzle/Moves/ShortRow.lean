import SlidingPuzzle.Algorithm.Parberry.RowSolve
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Moves.BlankAccess

/-! Short protected rows: pay the coarse first-column cost only once, then
use the ordinary Parberry placements. No whole-row budget is charged. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Place a nonempty row prefix with a spare column on its right. -/
theorem exists_short_row (B : Board n) (hn : 4 ≤ n) (a d : ℕ)
    (ha : a+2 < n) (hd0 : 1 ≤ d) (hd : d+1 ≤ n)
    (habove : ∀ x y : Fin n, x.val < a → B (x,y) = target n (x,y)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*d*n+504*n ∧ blank C = (⟨a+1,by omega⟩,⟨d-1,by omega⟩) ∧
      ∀ z : Cell n, z.1.val < a ∨ (z.1.val = a ∧ z.2.val < d) → C z = target n z := by
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  obtain ⟨w,hw,haboveW,_,_,hlenW⟩ := Zhong.placeStep a (by omega) ha hn 0 (by omega)
    B 0 (by omega) habove (by intros; omega) (by intros; omega) (by omega)
  have hfirst : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) →
      Zhong.actSeq B w z=target n z := by
    intro z hz
    rcases hz with hz | ⟨hx,hy⟩
    · exact haboveW z.1 z.2 hz
    · have he : z = (⟨a,by omega⟩,0) := by
        exact Prod.ext (Fin.ext hx) (Fin.ext (by change z.2.val=0; omega))
      rw [he]; exact hw
  obtain ⟨p,hp⟩ := path_of_zhong_word B w
  obtain ⟨D,q,hq,hbD,hD⟩ := Parberry.exists_row_start (Zhong.actSeq B w) a ha hfirst
  obtain ⟨C,r,hr,hbC,hC⟩ := Parberry.exists_row_prefix D a (d-1) ha (by omega) hbD hD
  have hbudget : Parberry.rowPrefixBudget n (d-1) ≤ (d-1)*(8*n) := by
    unfold Parberry.rowPrefixBudget
    calc
      _ ≤ ∑ j ∈ Finset.range (d-1), 8*n := Finset.sum_le_sum (fun j _ => Nat.sub_le _ _)
      _ = _ := by simp
  refine ⟨C,(p.append q).append r,?_,hbC,?_⟩
  · simp only [Path.length_append]
    have hw' : w.length ≤ 502*n := by nlinarith
    have hm := Nat.mul_le_mul_right (8*n) (Nat.sub_le d 1)
    nlinarith
  · intro z hz
    apply hC
    omega

/-- Include the final boundary column when the requested prefix fills the row.
Its linear cost is retained separately from the per-tile leading term. -/
theorem exists_short_row_with_boundary (B : Board n) (hn : 4 ≤ n) (a d : ℕ)
    (ha : a+2 < n) (hd0 : 1 ≤ d) (hd : d ≤ n)
    (habove : ∀ x y : Fin n, x.val < a → B (x,y) = target n (x,y)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*d*n+1008*n ∧ (blank C).1.val = a+1 ∧
      ∀ z : Cell n, z.1.val < a ∨ (z.1.val = a ∧ z.2.val < d) → C z = target n z := by
  by_cases hlast : d+1 ≤ n
  · obtain ⟨C,p,hp,hb,hC⟩ := exists_short_row B hn a d ha hd0 hlast habove
    exact ⟨C,p,by omega,by rw [hb],hC⟩
  have he : d=n := by omega
  subst d
  let : NeZero (n*n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  obtain ⟨D,p,hp,_,hD⟩ := exists_short_row B hn a (n-1) ha (by omega) (by omega) habove
  obtain ⟨w,hw,haboveW,_,hleft,hlen⟩ := Zhong.placeStep a (by omega) ha hn 0 (by omega)
    D (n-1) (by omega) (fun x y hx => hD (x,y) (Or.inl hx))
    (by intros; omega) (fun j hj => hD (⟨a,by omega⟩,j) (Or.inr ⟨rfl,hj⟩)) (by omega)
  have hW : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<n) →
      Zhong.actSeq D w z=target n z := by
    intro z hz
    rcases hz with hz | ⟨hx,hy⟩
    · exact haboveW z.1 z.2 hz
    · have hx' : z.1 = (⟨a,by omega⟩ : Fin n) := Fin.ext hx
      rw [show z=(⟨a,by omega⟩,z.2) from Prod.ext hx' rfl]
      by_cases hj : z.2.val < n-1
      · exact hleft z.2 hj
      · have hj' : z.2=(⟨n-1,by omega⟩ : Fin n) := Fin.ext (by change z.2.val=n-1; omega)
        rw [hj']; exact hw
  obtain ⟨q,hq⟩ := path_of_zhong_word D w
  obtain ⟨E,t,hbE,ht,hfix⟩ := exists_blank_access_path_preserving (Zhong.actSeq D w)
    (⟨a+1,by omega⟩,0)
  have hblankrow : a < (blank (Zhong.actSeq D w)).1.val := by
    by_contra hh
    have hz := hW (blank (Zhong.actSeq D w)) (by have := (blank (Zhong.actSeq D w)).2.isLt; omega)
    have hzero : target n (blank (Zhong.actSeq D w))=0 := hz.symm.trans ((Zhong.actSeq D w).apply_symm_apply 0)
    have hh := Zhong.target_ne_zero (blank (Zhong.actSeq D w)).1.val
      (blank (Zhong.actSeq D w)).2.val (blank (Zhong.actSeq D w)).2.isLt
      (by omega : (blank (Zhong.actSeq D w)).1.val+1<n)
    exact hh hzero
  refine ⟨E,(p.append q).append t,?_,by rw [hbE],?_⟩
  · have ht' : t.length ≤ 2*n := by
      apply ht.trans
      unfold gridDistance Nat.dist
      have := (blank (Zhong.actSeq D w)).1.isLt
      have := (blank (Zhong.actSeq D w)).2.isLt
      simp only [Fin.val_zero]
      omega
    simp only [Path.length_append]
    have hm := Nat.mul_le_mul_right (8*n) (Nat.sub_le n 1)
    nlinarith
  · intro z hz
    rw [hfix z (Or.inl (by
      change z.1.val < min (blank (Zhong.actSeq D w)).1.val (a+1)
      omega))]
    exact hW z hz

/-- The same short-row routine with arbitrary prescribed nonblank labels. -/
theorem exists_short_row_relabel (B T : Board n) (hn : 4 ≤ n)
    (hblank : blank T = blank (target n)) (a d : ℕ)
    (ha : a+2 < n) (hd0 : 1 ≤ d) (hd : d ≤ n)
    (habove : ∀ x y : Fin n, x.val < a → B (x,y) = T (x,y)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*d*n+1008*n ∧ (blank C).1.val = a+1 ∧
      ∀ z : Cell n, z.1.val < a ∨ (z.1.val = a ∧ z.2.val < d) → C z = T z := by
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e 0 = 0 := by
    change target n (blank T) = 0
    rw [hblank]
    exact (target n).apply_symm_apply 0
  have hes : e.symm 0 = 0 := by
    apply e.injective
    simp [he]
  obtain ⟨D,p,hp,hb,hD⟩ := exists_short_row_with_boundary (relabel B e) hn a d ha hd0 hd (by
    intro x y hx
    change target n (T.symm (B (x,y))) = _
    rw [habove x y hx,T.symm_apply_apply])
  have hq : ∃ q : Path B (relabel D e.symm), q.length ≤ 8*d*n+1008*n := by
    have h : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
        q.length ≤ 8*d*n+1008*n := ⟨p.relabel e.symm hes,by simpa using hp⟩
    rwa [relabel_relabel_symm] at h
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm,q,hq,by rwa [blank_relabel _ _ hes],?_⟩
  intro z hz
  change e.symm (D z) = T z
  rw [hD z hz]
  simp [e]
end SlidingPuzzle
