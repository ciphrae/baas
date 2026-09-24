import SlidingPuzzle.Bridge.Words
import Zhong.Algorithm.Lift

/-! Restriction and legal-word lifting for a rectangular unsolved region.
Labels are transported through the target, so solved outside cells are retained. -/
namespace SlidingPuzzle.Parberry.Rect
noncomputable section
open Zhong
variable {r c n : ℕ} [NeZero n]

/-- The local label corresponding to a cell is its ambient target label. -/
def labels (ι : Zhong.Cell r c ↪ SlidingPuzzle.Cell n) : Fin (r*c) ↪ Tile n :=
  (Zhong.target r c).symm.toEmbedding.trans (ι.trans (SlidingPuzzle.target n).toEmbedding)

omit [NeZero n] in
@[simp] theorem labels_target (ι : Zhong.Cell r c ↪ SlidingPuzzle.Cell n) (z : Zhong.Cell r c) :
    labels ι (Zhong.target r c z)=SlidingPuzzle.target n (ι z) := by
  simp [labels]

/-- Removing correctly placed outside cells yields an actual rectangular board. -/
theorem exists_board (ι : Zhong.Cell r c ↪ SlidingPuzzle.Cell n) (B : SlidingPuzzle.Board n)
    (hB : ∀ z : SlidingPuzzle.Cell n, z ∉ Set.range ι → B z=SlidingPuzzle.target n z) :
    ∃ A : Zhong.Board r c, ∀ z, B (ι z)=labels ι (A z) := by
  let pos := fun z : Zhong.Cell r c => (SlidingPuzzle.target n).symm (B (ι z))
  have hrange (z : Zhong.Cell r c) : pos z ∈ Set.range ι := by
    by_contra hh
    have he : pos z=ι z := B.injective ((hB (pos z) hh).trans ((SlidingPuzzle.target n).apply_symm_apply _))
    exact hh ⟨z,he.symm⟩
  let f := fun z => Classical.choose (hrange z)
  have he (z : Zhong.Cell r c) : ι (f z)=pos z := Classical.choose_spec (hrange z)
  have hinj : Function.Injective f := by
    intro x y h
    apply ι.injective
    apply B.injective
    apply (SlidingPuzzle.target n).symm.injective
    change pos x=pos y
    rw [← he x,← he y,h]
  let e : Zhong.Cell r c ≃ Zhong.Cell r c :=
    Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩
  refine ⟨e.trans (Zhong.target r c),?_⟩
  intro z
  change B (ι z)=labels ι (Zhong.target r c (f z))
  rw [labels_target,he]
  exact ((SlidingPuzzle.target n).apply_symm_apply _).symm

/-- Applicable rectangular words lift without touching the removed cells. -/
theorem exists_lifted_word [NeZero (r*c)]
    (ι : Zhong.Cell r c ↪ SlidingPuzzle.Cell n) (f : Dir → Dir)
    (hstep : ∀ (z : Zhong.Cell r c) δ z', neighbor? z δ=some z' →
      neighbor? (ι z) (f δ)=some (ι z'))
    (hzero : labels ι 0=0) (A : Zhong.Board r c) (B : SlidingPuzzle.Board n)
    (hB : ∀ z, B (ι z)=labels ι (A z)) (σ : List Dir)
    (happ : ApplicableFrom (Zhong.blank A) σ) :
    ∃ C : SlidingPuzzle.Board n, ∃ p : Path B C, p.length ≤ σ.length ∧
      (∀ z, C (ι z)=labels ι (actSeq A σ z)) ∧
      (∀ z : SlidingPuzzle.Cell n, z ∉ Set.range ι → C z=B z) := by
  have hblank : SlidingPuzzle.blank B=ι (Zhong.blank A) := by
    apply B.injective
    rw [hB]
    simpa only [SlidingPuzzle.blank,SlidingPuzzle.position,Zhong.blank,Equiv.apply_symm_apply] using hzero.symm
  obtain ⟨p,hp⟩ := path_of_zhong_word B (σ.map f)
  refine ⟨actSeq B (σ.map f),p,by simpa using hp,?_,?_⟩
  · intro z
    rw [actSeq_eq_permOf,actSeq_eq_permOf]
    change B (permOf (SlidingPuzzle.blank B) (σ.map f) (ι z))=labels ι (A (permOf (Zhong.blank A) σ z))
    rw [hblank,permOf_map_apply_of_neighbor_map ι.injective hstep _ _ happ,hB]
  · intro z hz
    rw [actSeq_eq_permOf]
    change B (permOf (SlidingPuzzle.blank B) (σ.map f) z)=B z
    rw [hblank,permOf_map_fixes_of_not_mem_range hstep _ _ happ hz]

end
end SlidingPuzzle.Parberry.Rect
