import SlidingPuzzle.Moves.ShortRow
import SlidingPuzzle.Moves.ProtectedTranslation
import SlidingPuzzle.Algorithm.Allocation

/-! Whole-family exchanges by shared staging, the paper's row-shift word,
and reversed staging. Boundary placement is paid once per family, not once
per three-cycle. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Stage two arbitrary nonblank families in adjacent row segments. -/
theorem exists_stage_families (B : Board n) (hn : 4 ≤ n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : 2*m ≤ n)
    (a b : Fin m ↪ Cell n) (hab : ∀ i j, a i ≠ b j)
    (ha : ∀ i, B (a i) ≠ 0) (hb : ∀ i, B (b i) ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 24*m*n+2020*n+6*m+2 ∧ blank C = (⟨2,by omega⟩,0) ∧
      (∀ i : Fin m, C (0,⟨i.val,by omega⟩) = B (a i)) ∧
      (∀ i : Fin m, C (⟨1,by omega⟩,⟨i.val,by omega⟩) = B (b i)) := by
  classical
  let u : Fin m ⊕ Fin m ↪ Cell n := ⟨fun i => match i with
    | .inl j => (0,⟨j.val,by omega⟩)
    | .inr j => (0,⟨m+j.val,by omega⟩), by
      intro i j h
      cases i <;> cases j <;> simp only [Prod.mk.injEq,Fin.mk.injEq,true_and] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · omega
      · omega
      · exact congrArg Sum.inr (Fin.ext (by omega))⟩
  let v : Fin m ⊕ Fin m ↪ Cell n := ⟨Sum.elim a b, by
    intro i j h
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg Sum.inl (a.injective h)
      | inr j => exact False.elim (hab i j h)
    | inr i => cases j with
      | inl j => exact False.elim (hab j i h.symm)
      | inr j => exact congrArg Sum.inr (b.injective h)⟩
  let f := v.trans B.toEmbedding
  obtain ⟨T,hT,hTu⟩ := exists_board_extending_cell_embedding u f
    (by intro i; cases i <;> exact Zhong.target_ne_zero 0 _ (by omega) (by omega))
    (by intro i; cases i with
        | inl i => exact ha i
        | inr i => exact hb i)
  obtain ⟨D,p,hp,hbD,hD⟩ := exists_short_row_relabel B T hn hT 0 (2*m)
    (by omega) (by omega) hmn (by intros; omega)
  have hDa (i : Fin m) : D (0,⟨i.val,by omega⟩) = B (a i) :=
    (hD _ (Or.inr ⟨rfl,by change i.val < 2*m; omega⟩)).trans (hTu (.inl i))
  have hDb (i : Fin m) : D (0,⟨m+i.val,by omega⟩) = B (b i) :=
    (hD _ (Or.inr ⟨rfl,by change m+i.val < 2*m; omega⟩)).trans (hTu (.inr i))
  obtain ⟨E,q,hbE,hq,hqfix⟩ := exists_blank_access_path_preserving D (⟨2,by omega⟩,⟨m,by omega⟩)
  have hq' : q.length ≤ 2*n := by
    apply hq.trans
    unfold gridDistance Nat.dist
    have := (blank D).1.isLt
    have := (blank D).2.isLt
    dsimp only
    omega
  have hEtop (j : Fin n) : E (0,j)=D (0,j) := hqfix _ (Or.inl (by simp [hbD]))
  obtain ⟨F,r,hr,hbF,hrowF,hfixF⟩ := exists_row_shift E 0 m m (by omega) (by omega) (by omega) hbE
  have hz : (⟨0,by omega⟩ : Fin n)=0 := Fin.ext (by simp)
  simp only [Nat.zero_add,hz] at hrowF
  have hFa (i : Fin m) : F (0,⟨i.val,by omega⟩) = B (a i) := by
    rw [hfixF _ (Or.inr (Or.inr (Or.inl i.isLt))),hEtop,hDa]
  have hFb (i : Fin m) : F (⟨1,by omega⟩,⟨m+i.val,by omega⟩) = B (b i) := by
    rw [hrowF,hEtop,hDb]
  let u' : Fin n ⊕ Fin m ↪ Cell n := ⟨fun i => match i with
    | .inl j => (0,j)
    | .inr j => (⟨1,by omega⟩,⟨j.val,by omega⟩), by
      intro i j h
      cases i <;> cases j
      · exact congrArg Sum.inl (Prod.mk.inj h).2
      · have hh := congrArg (fun x : Cell n => x.1.val) h
        norm_num at hh
      · have hh := congrArg (fun x : Cell n => x.1.val) h
        norm_num at hh
      · apply congrArg Sum.inr
        apply Fin.ext
        have hh := congrArg (fun x : Cell n => x.2.val) h
        dsimp at hh
        omega⟩
  let v' : Fin n ⊕ Fin m ↪ Cell n := ⟨fun i => match i with
    | .inl j => (0,j)
    | .inr j => (⟨1,by omega⟩,⟨m+j.val,by omega⟩), by
      intro i j h
      cases i <;> cases j
      · exact congrArg Sum.inl (Prod.mk.inj h).2
      · have hh := congrArg (fun x : Cell n => x.1.val) h
        norm_num at hh
      · have hh := congrArg (fun x : Cell n => x.1.val) h
        norm_num at hh
      · apply congrArg Sum.inr
        apply Fin.ext
        have hh := congrArg (fun x : Cell n => x.2.val) h
        dsimp at hh
        omega⟩
  obtain ⟨T',hT',hTu'⟩ := exists_board_extending_cell_embedding u' (v'.trans F.toEmbedding)
    (by
      intro i
      cases i with
      | inl j => exact Zhong.target_ne_zero 0 j.val j.isLt (by omega)
      | inr j => exact Zhong.target_ne_zero 1 j.val (by omega) (by omega))
    (by
      intro i hz
      have he : v' i = blank F := F.injective (hz.trans (F.apply_symm_apply 0).symm)
      rw [hbF,hbE] at he
      cases i with
      | inl j =>
        have hh := congrArg (fun x : Cell n => x.1.val) he
        change (0 : Fin n).val = 2 at hh
        simp at hh
      | inr j =>
        have hh := congrArg (fun x : Cell n => x.1.val) he
        change (1 : ℕ) = 2 at hh
        omega)
  obtain ⟨G,s,hs,hbG,hG⟩ := exists_short_row_relabel F T' hn hT' 1 m
    (by omega) (by omega) (by omega) (by
      intro x y hx
      have he : x=0 := Fin.ext (by change x.val=0; omega)
      subst x
      exact (hTu' (.inl y)).symm)
  have hGa (i : Fin m) : G (0,⟨i.val,by omega⟩)=B (a i) :=
    (hG _ (Or.inl (by simp))).trans ((hTu' (.inl _)).trans (hFa i))
  have hGb (i : Fin m) : G (⟨1,by omega⟩,⟨i.val,by omega⟩)=B (b i) :=
    (hG _ (Or.inr ⟨rfl,i.isLt⟩)).trans ((hTu' (.inr i)).trans (hFb i))
  obtain ⟨C,t,hbC,ht,hfixC⟩ := exists_blank_access_path_preserving G (⟨2,by omega⟩,0)
  have ht' : t.length ≤ 2*n := by
    apply ht.trans
    unfold gridDistance Nat.dist
    have := (blank G).1.isLt
    have := (blank G).2.isLt
    simp only [Fin.val_zero]
    omega
  refine ⟨C,(((p.append q).append r).append s).append t,?_,hbC,?_,?_⟩
  · simp only [Path.length_append]
    nlinarith
  · intro i
    rw [hfixC _ (Or.inl (by simp [hbG])),hGa]
  · intro i
    rw [hfixC _ (Or.inl (by simp [hbG])),hGb]

/-- A row shift exchanges the two data rows as sets, including odd widths.
Injectivity recovers the reverse membership without prescribing its order. -/
theorem exists_row_set_exchange (B : Board n) (hn : 4 ≤ n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hb : blank B = (⟨2,by omega⟩,0)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6*m+2 ∧ blank C = blank B ∧
      (∀ i : Fin m, ∃ j : Fin m, C (0,⟨i.val,by omega⟩) = B (⟨1,by omega⟩,⟨j.val,by omega⟩)) ∧
      (∀ i : Fin m, C (⟨1,by omega⟩,⟨i.val,by omega⟩) = B (0,⟨i.val,by omega⟩)) ∧
      ∀ x : Cell n, 2 ≤ x.1.val ∨ m ≤ x.2.val → C x = B x := by
  obtain ⟨C,p,hp,hbC,hrow,hfix⟩ := exists_row_shift B 0 0 m (by omega) (by omega) (by omega) hb
  have hz : (⟨0,by omega⟩ : Fin n)=0 := Fin.ext (by simp)
  simp only [Nat.zero_add,hz] at hrow
  refine ⟨C,p,hp,hbC,?_,hrow,?_⟩
  · intro i
    let x : Cell n := (0,⟨i.val,by omega⟩)
    let y := B.symm (C x)
    have hy : B y = C x := B.apply_symm_apply _
    have hyr : y.1.val < 2 := by
      by_contra hh
      have he : y=x := C.injective ((hfix y (Or.inr (Or.inl (by omega)))).trans hy)
      have he' := congrArg (fun z : Cell n => z.1.val) he
      dsimp [x] at he'
      omega
    have hyc : y.2.val < m := by
      by_contra hh
      have he : y=x := C.injective ((hfix y (Or.inr (Or.inr (Or.inr (by omega))))).trans hy)
      have he' := congrArg (fun z : Cell n => z.2.val) he
      dsimp [x] at he'
      omega
    have hyr1 : y.1.val = 1 := by
      by_contra hh
      have hy0 : y.1=0 := Fin.ext (by change y.1.val=0; omega)
      have hy' : y = (0,⟨y.2.val,by omega⟩) := Prod.ext hy0 rfl
      have hh := hrow ⟨y.2.val,hyc⟩
      rw [← hy',hy] at hh
      have he := congrArg (fun z : Cell n => z.1.val) (C.injective hh)
      change 1=0 at he
      omega
    refine ⟨⟨y.2.val,hyc⟩,?_⟩
    have hy' : y = (⟨1,by omega⟩,⟨y.2.val,by omega⟩) := Prod.ext (Fin.ext hyr1) rfl
    exact hy.symm.trans (congrArg B hy')
  · intro x hx
    apply hfix
    omega

/-- The paper's access / row exchange / reverse-access construction. The
linear boundary remainder is paid once for the whole pair of families. -/
theorem exists_bulk_family_exchange (B : Board n) (hn : 4 ≤ n) {m : ℕ}
    (hm : 2 ≤ m) (hmn : 2*m ≤ n)
    (a b : Fin m ↪ Cell n) (hab : ∀ i j, a i ≠ b j)
    (ha : ∀ i, B (a i) ≠ 0) (hb : ∀ i, B (b i) ≠ 0)
    (P Q : Tile n → Prop) (hP : ∀ i, P (B (a i))) (hQ : ∀ i, Q (B (b i))) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (48*m+4064)*n ∧ blank C = blank B ∧
      (∀ i, Q (C (a i))) ∧ (∀ i, P (C (b i))) ∧
      ∀ x, (∀ i, x ≠ a i) → (∀ i, x ≠ b i) → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDa,hDb⟩ := exists_stage_families B hn hm hmn a b hab ha hb
  obtain ⟨E,q,hq,hbE,hEa,hEb,hfix⟩ := exists_row_set_exchange D hn hm (by omega) hbD
  obtain ⟨C,r,hr,hbC,hC⟩ := p.exists_unstaged q hbE
  have hposa (i : Fin m) : D.symm (B (a i)) = (0,⟨i.val,by omega⟩) := by rw [← hDa i]; simp
  have hposb (i : Fin m) : D.symm (B (b i)) = (⟨1,by omega⟩,⟨i.val,by omega⟩) := by rw [← hDb i]; simp
  refine ⟨C,r,?_,hbC,?_,?_,?_⟩
  · nlinarith
  · intro i
    obtain ⟨j,hj⟩ := hEa i
    rw [hC,hposa,hj,hDb]
    exact hQ j
  · intro i
    rw [hC,hposb,hEb,hDa]
    exact hP i
  · intro x hxa hxb
    rw [hC,hfix]
    · exact D.apply_symm_apply (B x)
    · by_contra hh
      have hr : (D.symm (B x)).1.val < 2 := by omega
      have hc : (D.symm (B x)).2.val < m := by omega
      let i : Fin m := ⟨(D.symm (B x)).2.val,hc⟩
      by_cases hz : (D.symm (B x)).1.val=0
      · have he : D.symm (B x)=(0,⟨i.val,by omega⟩) := Prod.ext (Fin.ext hz) rfl
        have hh := congrArg D he
        rw [D.apply_symm_apply,hDa] at hh
        exact hxa i (B.injective hh)
      · have he : D.symm (B x)=(⟨1,by omega⟩,⟨i.val,by omega⟩) := Prod.ext (Fin.ext (by change (D.symm (B x)).1.val=1; omega)) rfl
        have hh := congrArg D he
        rw [D.apply_symm_apply,hDb] at hh
        exact hxb i (B.injective hh)
/-- The family exchange interface expressed directly with finite cell sets. -/
theorem exists_bulk_set_exchange (B : Board n) (hn : 4 ≤ n) (s t : Finset (Cell n))
    (hdis : Disjoint s t) (hcard : s.card = t.card) (hs : 2 ≤ s.card) (hsmall : 2*s.card ≤ n)
    (hs0 : ∀ x ∈ s, B x ≠ 0) (ht0 : ∀ x ∈ t, B x ≠ 0)
    (P Q : Tile n → Prop) (hP : ∀ x ∈ s, P (B x)) (hQ : ∀ x ∈ t, Q (B x)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (48*s.card+4064)*n ∧ blank C = blank B ∧
      (∀ x ∈ s, Q (C x)) ∧ (∀ x ∈ t, P (C x)) ∧
      ∀ x, x ∉ s → x ∉ t → C x = B x := by
  classical
  let ea := s.equivFin.symm
  let eb := (t.equivFinOfCardEq hcard.symm).symm
  let a : Fin s.card ↪ Cell n := ea.toEmbedding.trans (Function.Embedding.subtype _)
  let b : Fin s.card ↪ Cell n := eb.toEmbedding.trans (Function.Embedding.subtype _)
  have hab (i j) : a i ≠ b j := by
    intro h
    have hh : b j ∈ t := (eb j).property
    rw [← h] at hh
    exact Finset.disjoint_left.mp hdis (ea i).property hh
  obtain ⟨C,p,hp,hb,hCa,hCb,hfix⟩ := exists_bulk_family_exchange B hn hs hsmall a b hab
    (fun i => hs0 _ (ea i).property) (fun i => ht0 _ (eb i).property)
    P Q (fun i => hP _ (ea i).property) (fun i => hQ _ (eb i).property)
  refine ⟨C,p,hp,hb,?_,?_,?_⟩
  · intro x hx
    have hh := hCa (ea.symm ⟨x,hx⟩)
    simpa [a] using hh
  · intro x hx
    have hh := hCb (eb.symm ⟨x,hx⟩)
    simpa [b] using hh
  · intro x hxs hxt
    exact hfix x (fun i h => hxs (h ▸ (ea i).property))
      (fun i h => hxt (h ▸ (eb i).property))
end SlidingPuzzle
