import SlidingPuzzle.Algorithm.Parberry.RectEmbedding

/-! Solve the first column after the first row by transposing the remaining
rectangle. Its legal-word embedding fixes the entire solved row. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {m n : ℕ} [NeZero n]

/-- Coordinates in the transposed rectangle below the first row. -/
def columnEmbedding (hm : m+1=n) : Zhong.Cell n m ↪ SlidingPuzzle.Cell n where
  toFun z := (⟨z.2.val+1,by have := z.2.isLt; omega⟩,z.1)
  inj' := by
    intro x y h
    have hr := congrArg (fun z : SlidingPuzzle.Cell n => z.1.val) h
    have hc := congrArg (fun z : SlidingPuzzle.Cell n => z.2.val) h
    apply Prod.ext <;> apply Fin.ext <;> simp only at hr hc <;> omega

@[simp] theorem columnEmbedding_apply (hm : m+1=n) (z : Zhong.Cell n m) :
    columnEmbedding hm z=(⟨z.2.val+1,by have := z.2.isLt; omega⟩,z.1) := rfl

theorem columnEmbedding_range (hm : m+1=n) (z : SlidingPuzzle.Cell n) :
    z ∈ Set.range (columnEmbedding hm) ↔ 1 ≤ z.1.val := by
  constructor
  · rintro ⟨c,rfl⟩
    change 1 ≤ c.2.val+1
    omega
  · intro hz
    refine ⟨(z.2,⟨z.1.val-1,by have := z.1.isLt; omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change z.1.val-1+1=z.1.val; omega
    · rfl

/-- Only locally legal moves are transported across the removed boundary. -/
theorem columnEmbedding_neighbor (hm : m+1=n) (z : Zhong.Cell n m) (δ : Dir)
    (z' : Zhong.Cell n m) (h : neighbor? z δ=some z') :
    neighbor? (columnEmbedding hm z) (transDir δ)=some (columnEmbedding hm z') := by
  rcases z with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  cases δ with
  | U =>
      by_cases hs : i+1 < n
      · rw [neighbor?_mk_U hs] at h
        rw [← Option.some.inj h]
        simp [columnEmbedding_apply,transDir,neighbor?,hs]
      · simp [neighbor?,hs] at h
  | D =>
      by_cases hs : 0 < i
      · rw [neighbor?_mk_D hs] at h
        rw [← Option.some.inj h]
        simp [columnEmbedding_apply,transDir,neighbor?,hs]
      · simp [neighbor?,hs] at h
  | L =>
      by_cases hs : j+1 < m
      · rw [neighbor?_mk_L hs] at h
        rw [← Option.some.inj h]
        have hs' : j+1+1 < n := by omega
        simp [columnEmbedding_apply,transDir,neighbor?,hs']
      · simp [neighbor?,hs] at h
  | R =>
      by_cases hs : 0 < j
      · rw [neighbor?_mk_R hs] at h
        rw [← Option.some.inj h]
        simp [columnEmbedding_apply,transDir,neighbor?,Nat.sub_add_cancel hs]
      · simp [neighbor?,hs] at h

theorem columnEmbedding_labels_zero [NeZero (n*m)] (hm : m+1=n) (hm0 : 0 < m) :
    Rect.labels (columnEmbedding hm) 0=0 := by
  have hn0 : 0 < n := by omega
  have hnm : 1 < n*m := by nlinarith
  have ht := Zhong.target_last (n := n) (m := m) hn0 hm0 hnm
  have he : (Zhong.target n m).symm 0=(⟨n-1,by omega⟩,⟨m-1,by omega⟩) := by
    apply (Zhong.target n m).injective
    rw [Equiv.apply_symm_apply,ht]
  change SlidingPuzzle.target n (columnEmbedding hm ((Zhong.target n m).symm 0))=0
  rw [he]
  have hcorner : columnEmbedding hm (⟨n-1,by omega⟩,⟨m-1,by omega⟩)=
      ((⟨n-1,by omega⟩ : Fin n),(⟨n-1,by omega⟩ : Fin n)) := by
    apply Prod.ext <;> apply Fin.ext
    · change m-1+1=n-1; omega
    · rfl
  rw [hcorner]
  exact target_bottomRight n

/-- Complete the first column while preserving the already solved first row. -/
theorem exists_complete_column (B : SlidingPuzzle.Board n) (hn : 5 ≤ n)
    (hrow : ∀ y : Fin n, B (0,y)=SlidingPuzzle.target n (0,y)) :
    ∃ C : SlidingPuzzle.Board n, ∃ p : Path B C,
      2*p.length ≤ 15*n^2+3002*n+1 ∧
      (∀ y : Fin n, C (0,y)=B (0,y)) ∧
      (∀ x : Fin n, C (x,0)=SlidingPuzzle.target n (x,0)) := by
  let m := n-1
  have hm : m+1=n := by dsimp [m]; omega
  have hm4 : 4 ≤ m := by dsimp [m]; omega
  letI : NeZero (n*m) := ⟨by nlinarith⟩
  let ι := columnEmbedding hm
  have hB : ∀ z : SlidingPuzzle.Cell n, z ∉ Set.range ι → B z=SlidingPuzzle.target n z := by
    intro z hz
    have hr : z.1=0 := by
      apply Fin.ext
      have := (columnEmbedding_range hm z).not.mp hz
      simp only [Fin.val_zero]; omega
    change B (z.1,z.2)=SlidingPuzzle.target n (z.1,z.2)
    rw [hr]
    exact hrow z.2
  obtain ⟨A,hA⟩ := Rect.exists_board ι B hB
  obtain ⟨σ,hlen,happ,_,hσ⟩ := Rect.exists_complete_row_word A 0 (by omega) hm4 (by omega)
    (by intros; omega)
  obtain ⟨C,p,hp,hC,hfix⟩ := Rect.exists_lifted_word ι transDir (columnEmbedding_neighbor hm)
    (columnEmbedding_labels_zero hm (by omega)) A B hA σ happ
  refine ⟨C,p,by omega,?_,?_⟩
  · intro y
    apply hfix
    rw [columnEmbedding_range]
    simp
  · intro x
    by_cases hx : x.val=0
    · have he : x=0 := Fin.ext hx
      rw [he,hfix _ (by rw [columnEmbedding_range]; simp)]
      exact hrow 0
    · let y : Fin m := ⟨x.val-1,by have := x.isLt; omega⟩
      have he : ι ((⟨0,by omega⟩ : Fin n),y)=(x,0) := by
        apply Prod.ext <;> apply Fin.ext
        · change x.val-1+1=x.val; omega
        · rfl
      rw [← he,hC,hσ,Rect.labels_target]

end SlidingPuzzle.Parberry
