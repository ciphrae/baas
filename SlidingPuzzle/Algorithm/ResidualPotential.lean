import SlidingPuzzle.Algorithm.Residual
import SlidingPuzzle.Algorithm.Accounting

/-! The solved prefix contributes zero, and corner relabeling preserves distance. -/
namespace SlidingPuzzle
noncomputable section
open Classical
variable {m n : ℕ} [NeZero m] [NeZero n]

theorem manhattan_eq_sum_cells (B : Board n) :
    manhattan B = ∑ c : Cell n,
      if B c = 0 then 0 else gridDistance c (position (target n) (B c)) := by
  unfold manhattan
  symm
  apply Fintype.sum_equiv B
  intro c
  have hz : (B c).val = 0 ↔ B c = 0 := by
    constructor
    · exact fun h => Fin.ext h
    · exact fun h => congrArg Fin.val h
  simp only [position, Equiv.symm_apply_apply, hz]

omit [NeZero m] [NeZero n] in
theorem position_target_cornerLabels (d : ℕ) (hd : d+m=n) (t : Tile m) :
    position (target n) (cornerLabels d hd t) =
      cornerEmbedding d hd (position (target m) t) := by
  apply (target n).injective
  simp [position, cornerLabels]

/-- Removing solved outer rows and columns preserves the entire remaining potential. -/
theorem residual_manhattan_eq (d : ℕ) (hd : d+m=n) (B : Board n)
    (hB : ∀ x y : Fin n, x.val<d ∨ y.val<d → B (x,y)=target n (x,y))
    (A : Board m) (hA : ∀ c, B (cornerEmbedding d hd c)=cornerLabels d hd (A c)) :
    manhattan B = manhattan A := by
  let f : Cell n → ℕ := fun c =>
    if B c = 0 then 0 else gridDistance c (position (target n) (B c))
  have hin (c : Cell m) : f (cornerEmbedding d hd c) =
      if A c = 0 then 0 else gridDistance c (position (target m) (A c)) := by
    have hz : cornerLabels d hd (A c) = 0 ↔ A c = 0 := by
      rw [← cornerLabels_zero d hd]
      exact (cornerLabels d hd).injective.eq_iff
    simp only [f, hA, hz, position_target_cornerLabels, cornerEmbedding_distance]
  have hout (c : Cell n) (hc : c ∉ Finset.univ.map (cornerEmbedding d hd)) : f c = 0 := by
    have hp : c.1.val<d ∨ c.2.val<d := by
      by_contra hp
      have hr := c.1.isLt
      have hc' := c.2.isLt
      have he : ∃ a : Cell m, cornerEmbedding d hd a = c := by
        refine ⟨(⟨c.1.val-d,by omega⟩,⟨c.2.val-d,by omega⟩),?_⟩
        apply Prod.ext <;> apply Fin.ext
        · change d+(c.1.val-d)=c.1.val; omega
        · change d+(c.2.val-d)=c.2.val; omega
      exact hc (by simpa using he)
    simp [f, hB c.1 c.2 hp, position]
  rw [manhattan_eq_sum_cells B, manhattan_eq_sum_cells A]
  change (∑ c, f c) = _
  calc
    (∑ c, f c) = ∑ c ∈ Finset.univ.map (cornerEmbedding d hd), f c := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro c _ hc
      exact hout c hc
    _ = ∑ c : Cell m, f (cornerEmbedding d hd c) := Finset.sum_map _ _ _
    _ = _ := Finset.sum_congr rfl (fun c _ => hin c)

/-- The residual approximation lifts with at most twice the prefix length in overhead. -/
theorem optimalLength_le_prefix_residual_solution (X : ReachableBoard n)
    (d : ℕ) (hd : d+m=n) (B : Board n) (p : Path X.val B)
    (hB : ∀ x y : Fin n, x.val<d ∨ y.val<d → B (x,y)=target n (x,y))
    (A : Board m) (hA : ∀ c, B (cornerEmbedding d hd c)=cornerLabels d hd (A c))
    (q : Path A (target m)) {E : ℕ} (hq : q.length ≤ manhattan A + E) :
    optimalLength X ≤ manhattan X.val + 2*p.length + E := by
  obtain ⟨q',hq'⟩ := residual_solution_lifts d hd B hB A hA q
  apply optimalLength_le_prefix_solution X p q'
  rw [hq', residual_manhattan_eq d hd B hB A hA]
  exact hq

end
end SlidingPuzzle
