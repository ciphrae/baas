import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Parberry.RectRow
import SlidingPuzzle.Parberry.RectEmbedding
import SlidingPuzzle.Parberry.RowSolve
import SlidingPuzzle.Moves.Transpose

/-! A prefix solving the first `d` columns and the first `r` rows. Columns are
solved one at a time (by transposing the row solver), so the leading cost is
about half that of solving `d` complete layers when `r` is much smaller than `d`.
The remaining rows lie in the rectangle to the right of the solved columns. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n : ℕ} [NeZero n]

/-- Solve the first `d` rows, each protecting the rows above it. -/
theorem exists_rows_prefix (B : Board n) (hn : 4 ≤ n) (d : ℕ) (hd : d+2 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, 2*p.length ≤ d*(15*n^2+3002*n+1) ∧
      ∀ x y : Fin n, x.val<d → C (x,y)=target n (x,y) := by
  induction d with
  | zero => exact ⟨B, Path.nil B, by simp, by intros; omega⟩
  | succ d ih =>
    obtain ⟨C, p, hp, hC⟩ := ih (by omega)
    obtain ⟨D, q, hq, hfix, hrow⟩ := exists_complete_row C d (by omega) hn hC
    refine ⟨D, p.append q, ?_, ?_⟩
    · rw [Path.length_append]
      have he : (d+1)*(15*n^2+3002*n+1) = d*(15*n^2+3002*n+1)+(15*n^2+3002*n+1) := by ring
      omega
    · intro x y hx
      by_cases hxd : x.val<d
      · rw [hfix x y hxd]; exact hC x y hxd
      · have he : x=⟨d,by omega⟩ := Fin.ext (by show x.val=d; omega)
        rw [he]; exact hrow y

/-- Transfer a construction toward the standard target to an arbitrary target
with the same blank cell, by relabelling tiles. -/
theorem exists_relabeled {P : ℕ → Prop} {R : Cell n → Prop}
    (h : ∀ B : Board n, ∃ C : Board n, ∃ p : Path B C, P p.length ∧
      ∀ c, R c → C c=target n c)
    (B T : Board n) (hT : blank T=blank (target n)) :
    ∃ C : Board n, ∃ p : Path B C, P p.length ∧ ∀ c, R c → C c=T c := by
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e 0=0 := by
    change target n (blank T)=0
    rw [hT]
    simp [blank,position]
  have hes : e.symm 0=0 := by
    apply e.injective
    simp [he]
  obtain ⟨D,p,hp,hD⟩ := h (relabel B e)
  have hq : ∃ q : Path B (relabel D e.symm), q.length=p.length := by
    have hh : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
        q.length=p.length := ⟨p.relabel e.symm hes,by simp⟩
    rwa [relabel_relabel_symm] at hh
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm,q,by rw [hq]; exact hp,?_⟩
  intro c hc
  change e.symm (D c)=T c
  rw [hD c hc]
  simp [e]

theorem blank_target_swap : (blank (target n)).swap=blank (target n) := by
  have ht : blank (target n)=
      (⟨n-1,by have := NeZero.pos n; omega⟩,⟨n-1,by have := NeZero.pos n; omega⟩) := by
    apply (target n).injective
    rw [target_bottomRight]
    simp [blank,position]
  rw [ht]; rfl

/-- Solve the first `d` columns toward an arbitrary target with the standard
blank cell. -/
theorem exists_columns_prefix (B T : Board n) (hT : blank T=blank (target n))
    (hn : 4 ≤ n) (d : ℕ) (hd : d+2 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, 2*p.length ≤ d*(15*n^2+3002*n+1) ∧
      ∀ x y : Fin n, y.val<d → C (x,y)=T (x,y) := by
  have hT' : blank (transposeBoard T)=blank (target n) := by
    rw [blank_transposeBoard,hT,blank_target_swap]
  obtain ⟨C,p,hp,hC⟩ := exists_relabeled (P := fun l => 2*l ≤ d*(15*n^2+3002*n+1))
    (R := fun c : Cell n => c.1.val<d)
    (fun B => by
      obtain ⟨C,p,hp,hC⟩ := exists_rows_prefix B hn d hd
      exact ⟨C,p,hp,fun c hc => hC c.1 c.2 hc⟩)
    (transposeBoard B) (transposeBoard T) hT'
  have hq : ∃ q : Path B (transposeBoard C), q.length=p.length := by
    have hh := p.exists_transpose
    rwa [transposeBoard_transposeBoard] at hh
  obtain ⟨q,hq⟩ := hq
  refine ⟨transposeBoard C,q,by rw [hq]; exact hp,?_⟩
  intro x y hy
  change C (y,x)=T (x,y)
  exact hC (y,x) hy

/-- The rectangle to the right of the first `d` columns. -/
def shiftEmbedding (d m : ℕ) (hm : d+m=n) : Zhong.Cell n m ↪ SlidingPuzzle.Cell n where
  toFun z := (z.1,⟨z.2.val+d,by have := z.2.isLt; omega⟩)
  inj' := by
    intro x y h
    have hr := congrArg (fun z : SlidingPuzzle.Cell n => z.1) h
    have hc := congrArg (fun z : SlidingPuzzle.Cell n => z.2.val) h
    simp only at hr hc
    exact Prod.ext hr (Fin.ext (by omega))

omit [NeZero n] in
@[simp] theorem shiftEmbedding_apply {d m : ℕ} (hm : d+m=n) (z : Zhong.Cell n m) :
    shiftEmbedding d m hm z=(z.1,⟨z.2.val+d,by have := z.2.isLt; omega⟩) := rfl

omit [NeZero n] in
theorem shiftEmbedding_range {d m : ℕ} (hm : d+m=n) (z : SlidingPuzzle.Cell n) :
    z ∈ Set.range (shiftEmbedding d m hm) ↔ d ≤ z.2.val := by
  constructor
  · rintro ⟨c,rfl⟩
    change d ≤ c.2.val+d
    omega
  · intro hz
    refine ⟨(z.1,⟨z.2.val-d,by have := z.2.isLt; omega⟩),?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext; change z.2.val-d+d=z.2.val; omega

omit [NeZero n] in
theorem shiftEmbedding_neighbor {d m : ℕ} (hm : d+m=n) (z : Zhong.Cell n m) (δ : Dir)
    (z' : Zhong.Cell n m) (h : neighbor? z δ=some z') :
    neighbor? (shiftEmbedding d m hm z) δ=some (shiftEmbedding d m hm z') := by
  rcases z with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  cases δ with
  | U =>
      by_cases hs : i+1 < n
      · rw [neighbor?_mk_U hs] at h
        cases h
        simp only [shiftEmbedding_apply]
        rw [neighbor?_mk_U (x := ⟨i,hi⟩) (y := ⟨j+d,by omega⟩) hs]
      · simp [neighbor?,hs] at h
  | D =>
      by_cases hs : 0 < i
      · rw [neighbor?_mk_D hs] at h
        cases h
        simp only [shiftEmbedding_apply]
        rw [neighbor?_mk_D (x := ⟨i,hi⟩) (y := ⟨j+d,by omega⟩) hs]
      · simp [neighbor?,hs] at h
  | L =>
      by_cases hs : j+1 < m
      · rw [neighbor?_mk_L hs] at h
        cases h
        simp only [shiftEmbedding_apply]
        rw [neighbor?_mk_L (x := ⟨i,hi⟩) (y := ⟨j+d,by omega⟩) (by simp only; omega)]
        simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, true_and]
        omega
      · simp [neighbor?,hs] at h
  | R =>
      by_cases hs : 0 < j
      · rw [neighbor?_mk_R hs] at h
        cases h
        simp only [shiftEmbedding_apply]
        rw [neighbor?_mk_R (x := ⟨i,hi⟩) (y := ⟨j+d,by omega⟩) (by simp only; omega)]
        simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, true_and]
        omega
      · simp [neighbor?,hs] at h

theorem shiftEmbedding_labels_zero {d m : ℕ} [NeZero (n*m)] (hm : d+m=n) (hm2 : 2 ≤ m) :
    Rect.labels (shiftEmbedding d m hm) 0=0 := by
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hnm : 1 < n*m := by nlinarith
  have ht := Zhong.target_last (n := n) (m := m) hn0 hm0 hnm
  have he : (Zhong.target n m).symm 0=(⟨n-1,by omega⟩,⟨m-1,by omega⟩) := by
    apply (Zhong.target n m).injective
    rw [Equiv.apply_symm_apply,ht]
  change SlidingPuzzle.target n (shiftEmbedding d m hm ((Zhong.target n m).symm 0))=0
  rw [he]
  have hcorner : shiftEmbedding d m hm (⟨n-1,by omega⟩,⟨m-1,by omega⟩)=
      ((⟨n-1,by omega⟩ : Fin n),(⟨n-1,by omega⟩ : Fin n)) := by
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change m-1+d=n-1; omega
  rw [hcorner]
  exact target_bottomRight n

/-- After the first `d` columns, solve the first `r` rows of the remaining
rectangle. Each row of the rectangle costs at most the square-row budget. -/
theorem exists_right_rows (B : Board n) (d r : ℕ) (hm4 : d+4 ≤ n) (hr : r+2 ≤ n)
    (hleft : ∀ x y : Fin n, y.val<d → B (x,y)=target n (x,y)) :
    ∃ C : Board n, ∃ p : Path B C, 2*p.length ≤ r*(15*n^2+3002*n+1) ∧
      ∀ x y : Fin n, x.val<r ∨ y.val<d → C (x,y)=target n (x,y) := by
  let m := n-d
  have hm : d+m=n := by dsimp [m]; omega
  letI : NeZero (n*m) := ⟨Nat.mul_ne_zero (NeZero.ne n) (by dsimp [m]; omega)⟩
  let ι := shiftEmbedding d m hm
  induction r with
  | zero => exact ⟨B, Path.nil B, by simp, fun x y h => by
      rcases h with h | h
      · omega
      · exact hleft x y h⟩
  | succ r ih =>
    obtain ⟨C, p, hp, hC⟩ := ih (by omega)
    have hout : ∀ z : SlidingPuzzle.Cell n, z ∉ Set.range ι → C z=SlidingPuzzle.target n z := by
      intro z hz
      have hz' : z.2.val<d := by
        by_contra h
        exact hz ((shiftEmbedding_range hm z).mpr (by omega))
      exact hC z.1 z.2 (Or.inr hz')
    obtain ⟨A,hA⟩ := Rect.exists_board ι C hout
    have habove : ∀ (x : Fin n) (y : Fin m), x.val<r → A (x,y)=Zhong.target n m (x,y) := by
      intro x y hx
      apply (Rect.labels ι).injective
      rw [← hA, Rect.labels_target]
      exact hC _ _ (Or.inl hx)
    obtain ⟨σ,hlen,happ,hfixσ,hrowσ⟩ := Rect.exists_complete_row_word A r (by omega)
      (by dsimp [m]; omega) (by dsimp [m]; omega) habove
    obtain ⟨D,q,hq,hD,hfix⟩ := Rect.exists_lifted_word ι id
      (fun z δ z' h => shiftEmbedding_neighbor hm z δ z' h)
      (shiftEmbedding_labels_zero hm (by dsimp [m]; omega)) A C hA σ happ
    refine ⟨D, p.append q, ?_, ?_⟩
    · rw [Path.length_append]; nlinarith
    · intro x y hxy
      by_cases hy : y.val<d
      · rw [hfix (x,y) (by rw [shiftEmbedding_range]; exact not_le.mpr hy)]
        exact hC x y (Or.inr hy)
      · let z : Zhong.Cell n m := (x,⟨y.val-d,by have := y.isLt; dsimp [m]; omega⟩)
        have hz : ι z=(x,y) := by
          apply Prod.ext
          · rfl
          · apply Fin.ext; change y.val-d+d=y.val; omega
        rw [← hz, hD]
        by_cases hx : x.val<r
        · rw [hfixσ x _ hx, ← hA, hz]
          exact hC x y (Or.inl hx)
        · have hxr : x=⟨r,by omega⟩ := Fin.ext (by show x.val=r; omega)
          have := hrowσ z.2
          rw [← hxr] at this
          rw [this, Rect.labels_target]

/-- The mixed prefix toward an arbitrary target with the standard blank. -/
theorem exists_mixed_prefix (B T : Board n) (hT : blank T=blank (target n))
    (hn : 4 ≤ n) (r d : ℕ) (hd : d+4 ≤ n) (hr : r+2 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C, 2*p.length ≤ (d+r)*(15*n^2+3002*n+1) ∧
      ∀ x y : Fin n, x.val<r ∨ y.val<d → C (x,y)=T (x,y) := by
  obtain ⟨C,p,hp,hC⟩ := exists_relabeled
    (P := fun l => 2*l ≤ (d+r)*(15*n^2+3002*n+1))
    (R := fun c : Cell n => c.1.val<r ∨ c.2.val<d)
    (fun B => by
      obtain ⟨C₁,p₁,hp₁,hC₁⟩ := exists_columns_prefix B (target n) rfl hn d (by omega)
      obtain ⟨C₂,p₂,hp₂,hC₂⟩ := exists_right_rows C₁ d r hd hr hC₁
      refine ⟨C₂,p₁.append p₂,?_,fun c hc => hC₂ c.1 c.2 hc⟩
      rw [Path.length_append]; nlinarith)
    B T hT
  exact ⟨C,p,hp,fun x y h => hC (x,y) h⟩

end SlidingPuzzle.Parberry
