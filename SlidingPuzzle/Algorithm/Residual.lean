import SlidingPuzzle.Moves.Embedding
import SlidingPuzzle.Target

/-! Canonical coordinates and labels for the square remaining after an outer prefix. -/
namespace SlidingPuzzle
noncomputable section
variable {m n : ℕ} [NeZero m] [NeZero n]

def cornerEmbedding (d : ℕ) (hd : d+m=n) : Cell m ↪ Cell n where
  toFun c := (⟨d+c.1.val,by have := c.1.isLt; omega⟩,
    ⟨d+c.2.val,by have := c.2.isLt; omega⟩)
  inj' := by
    intro a b h
    have h1 := congrArg (fun c : Cell n => c.1.val) h
    have h2 := congrArg (fun c : Cell n => c.2.val) h
    simp only at h1 h2
    apply Prod.ext <;> apply Fin.ext <;> omega

omit [NeZero m] in
theorem cornerEmbedding_distance (d : ℕ) (hd : d+m=n) (a b : Cell m) :
    gridDistance (cornerEmbedding d hd a) (cornerEmbedding d hd b)=gridDistance a b := by
  change Nat.dist (d+a.1.val) (d+b.1.val) + Nat.dist (d+a.2.val) (d+b.2.val) = _
  simp only [gridDistance,Nat.dist]
  omega

def cornerLabels (d : ℕ) (hd : d+m=n) : Tile m ↪ Tile n :=
  (target m).symm.toEmbedding.trans ((cornerEmbedding d hd).trans (target n).toEmbedding)

omit [NeZero m] in
@[simp] theorem cornerLabels_target (d : ℕ) (hd : d+m=n) (c : Cell m) :
    cornerLabels d hd (target m c)=target n (cornerEmbedding d hd c) := by
  simp [cornerLabels]

theorem cornerLabels_zero (d : ℕ) (hd : d+m=n) : cornerLabels d hd 0=0 := by
  have hm := NeZero.pos m
  have he : position (target m) 0 =
      (⟨m-1,by omega⟩,⟨m-1,by omega⟩) := by
    apply (target m).injective
    rw [target_bottomRight]
    exact (target m).apply_symm_apply 0
  change target n (cornerEmbedding d hd (position (target m) 0))=0
  rw [he]
  have hc : cornerEmbedding d hd (⟨m-1,by omega⟩,⟨m-1,by omega⟩) =
      (⟨n-1,by have := NeZero.pos n; omega⟩,⟨n-1,by have := NeZero.pos n; omega⟩) := by
    apply Prod.ext <;> apply Fin.ext <;> change d+(m-1)=n-1 <;> omega
  rw [hc]
  exact target_bottomRight n

omit [NeZero m] in
/-- After a solved outer prefix, every remaining tile's target is in the remaining square. -/
theorem residual_target_inside (d : ℕ) (hd : d+m=n) (B : Board n)
    (hB : ∀ x y : Fin n, x.val<d ∨ y.val<d → B (x,y)=target n (x,y))
    (c : Cell m) :
    d ≤ (position (target n) (B (cornerEmbedding d hd c))).1.val ∧
    d ≤ (position (target n) (B (cornerEmbedding d hd c))).2.val := by
  let x := position (target n) (B (cornerEmbedding d hd c))
  have hnot : ¬ (x.1.val<d ∨ x.2.val<d) := by
    intro h
    have he : x=cornerEmbedding d hd c := B.injective
      ((hB x.1 x.2 h).trans ((target n).apply_symm_apply _))
    rw [he] at h
    change d+c.1.val<d ∨ d+c.2.val<d at h
    omega
  dsimp [x] at hnot
  omega
/-- The unsolved corner can be relabeled as an actual smaller puzzle board. -/
theorem exists_residual_board (d : ℕ) (hd : d+m=n) (B : Board n)
    (hB : ∀ x y : Fin n, x.val<d ∨ y.val<d → B (x,y)=target n (x,y)) :
    ∃ A : Board m, ∀ c, B (cornerEmbedding d hd c)=cornerLabels d hd (A c) := by
  let pos := fun c : Cell m => position (target n) (B (cornerEmbedding d hd c))
  have hp (c : Cell m) : d ≤ (pos c).1.val ∧ d ≤ (pos c).2.val :=
    residual_target_inside d hd B hB c
  let f : Cell m → Cell m := fun c =>
    (⟨(pos c).1.val-d,by have := (pos c).1.isLt; have := hp c; omega⟩,
     ⟨(pos c).2.val-d,by have := (pos c).2.isLt; have := hp c; omega⟩)
  have he (c : Cell m) : cornerEmbedding d hd (f c)=pos c := by
    apply Prod.ext <;> apply Fin.ext
    · change d+((pos c).1.val-d)=(pos c).1.val
      have := hp c; omega
    · change d+((pos c).2.val-d)=(pos c).2.val
      have := hp c; omega
  have hinj : Function.Injective f := by
    intro a b hab
    have hpos : pos a=pos b := by rw [← he a,← he b,hab]
    apply (cornerEmbedding d hd).injective
    apply B.injective
    exact (target n).symm.injective hpos
  let e : Cell m ≃ Cell m := Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩
  refine ⟨e.trans (target m),?_⟩
  intro c
  change B (cornerEmbedding d hd c)=cornerLabels d hd (target m (f c))
  rw [cornerLabels_target,he]
  exact ((target n).apply_symm_apply _).symm

/-- A solution of the relabeled residual lifts to a full solution with no added moves. -/
theorem residual_solution_lifts (d : ℕ) (hd : d+m=n) (B : Board n)
    (hB : ∀ x y : Fin n, x.val<d ∨ y.val<d → B (x,y)=target n (x,y))
    (A : Board m) (hA : ∀ c, B (cornerEmbedding d hd c)=cornerLabels d hd (A c))
    (p : Path A (target m)) : ∃ q : Path B (target n), q.length=p.length := by
  obtain ⟨C,q,hq,hC,hfix⟩ := p.exists_embedded (cornerEmbedding d hd)
    (fun a b h => by rw [cornerEmbedding_distance]; exact h)
    (cornerLabels d hd) (cornerLabels_zero d hd) B hA
  have he : C=target n := by
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ Set.range (cornerEmbedding d hd)
    · obtain ⟨c,rfl⟩ := hx
      rw [hC,cornerLabels_target]
    · rw [hfix x hx]
      apply hB
      by_contra h
      have hrow := x.1.isLt
      have hcol := x.2.isLt
      have hm : d ≤ x.1.val ∧ d ≤ x.2.val := by omega
      apply hx
      refine ⟨(⟨x.1.val-d,by omega⟩,⟨x.2.val-d,by omega⟩),?_⟩
      apply Prod.ext <;> apply Fin.ext
      · change d+(x.1.val-d)=x.1.val; omega
      · change d+(x.2.val-d)=x.2.val; omega
  have h : ∃ q : Path B C, q.length=p.length := ⟨q,hq⟩
  rw [he] at h
  exact h

end
end SlidingPuzzle
