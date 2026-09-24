import SlidingPuzzle.Moves.ThreeCycle

/-! Exchanges of tile sets, including the parity correction for odd set sizes. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Two disjoint swaps preserve parity and can be performed with two three-cycles. -/
theorem exists_double_swap (B : Board n) (hn : 4 ≤ n)
    (a b c d : Cell n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : B a ≠ 0) (hb : B b ≠ 0) (hc : B c ≠ 0) (hd : B d ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6044*n ∧ blank C = blank B ∧
      C a = B c ∧ C b = B d ∧ C c = B a ∧ C d = B b ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDa,hDb,hDc,hfixD⟩ :=
    exists_three_cycle B hn a b c hab hac hbc ha hb hc
  have hDd : D d = B d := hfixD d had.symm hbd.symm hcd.symm
  obtain ⟨C,q,hq,hbC,hCa,hCb,hCd,hfixC⟩ := exists_three_cycle D hn a b d
    hab had hbd (by rwa [hDa]) (by rwa [hDb]) (by rwa [hDd])
  refine ⟨C,p.append q,?_,hbC.trans hbD,hCa.trans hDb,hCb.trans hDd,?_,
    hCd.trans hDa,?_⟩
  · rw [Path.length_append]; omega
  · exact (hfixC c hac.symm hbc.symm hcd).trans hDc
  · intro x hxa hxb hxc hxd
    rw [hfixC x hxa hxb hxd,hfixD x hxa hxb hxc]

private theorem nonzero_of_same_blank {B C : Board n} (h : blank C = blank B)
    {x : Cell n} (hx : B x ≠ 0) : C x ≠ 0 := by
  intro hz
  have he : x = blank C := C.injective (hz.trans (C.apply_symm_apply 0).symm)
  apply hx
  rw [he,h]
  exact B.apply_symm_apply 0

/-- Exchange two disjoint nonblank families of equal size at least two. Membership
is exchanged exactly; order within each family is allowed to change. Two cells in
one family absorb the parity correction, so odd family sizes are included. -/
theorem exists_family_exchange (B : Board n) (hn : 4 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (a b : Fin m ↪ Cell n) (hab : ∀ i j, a i ≠ b j)
    (ha : ∀ i, B (a i) ≠ 0) (hb : ∀ i, B (b i) ≠ 0)
    (P Q : Tile n → Prop) (hP : ∀ i, P (B (a i))) (hQ : ∀ i, Q (B (b i))) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6044*m*n ∧ blank C = blank B ∧
      (∀ i, Q (C (a i))) ∧ (∀ i, P (C (b i))) ∧
      ∀ x, (∀ i, x ≠ a i) → (∀ i, x ≠ b i) → C x = B x := by
  let z : Fin m := ⟨0,by omega⟩
  let o : Fin m := ⟨1,by omega⟩
  have hzo : z ≠ o := by simp [z,o,Fin.ext_iff]
  have ha01 : a z ≠ a o := a.injective.ne hzo
  have hb01 : b z ≠ b o := b.injective.ne hzo
  have step (d : ℕ) (hd : 2 ≤ d) (hdm : d ≤ m) :
      ∃ C : Board n, ∃ p : Path B C,
        p.length ≤ 6044*(d-1)*n ∧ blank C = blank B ∧
        (∀ i : Fin m, i.val < d → Q (C (a i))) ∧
        (∀ i : Fin m, i.val < d → P (C (b i))) ∧
        (∀ i : Fin m, d ≤ i.val → C (a i) = B (a i) ∧ C (b i) = B (b i)) ∧
        (∀ x, (∀ i, x ≠ a i) → (∀ i, x ≠ b i) → C x = B x) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      by_cases hd2 : d = 2
      · subst d
        obtain ⟨C,p,hp,hbC,haz,hao,hbz,hbo,hfix⟩ := exists_double_swap B hn
          (a z) (a o) (b z) (b o) ha01 (hab z z) (hab z o)
          (hab o z) (hab o o) hb01 (ha z) (ha o) (hb z) (hb o)
        refine ⟨C,p,by simpa using hp,hbC,?_,?_,?_,?_⟩
        · intro i hi
          have he : i=z ∨ i=o := by
            by_cases hh : i.val=0
            · exact Or.inl (Fin.ext hh)
            · exact Or.inr (Fin.ext (by dsimp [o]; omega))
          rcases he with rfl | rfl
          · rw [haz]; exact hQ z
          · rw [hao]; exact hQ o
        · intro i hi
          have he : i=z ∨ i=o := by
            by_cases hh : i.val=0
            · exact Or.inl (Fin.ext hh)
            · exact Or.inr (Fin.ext (by dsimp [o]; omega))
          rcases he with rfl | rfl
          · rw [hbz]; exact hP z
          · rw [hbo]; exact hP o
        · intro i hi
          have hiz : i ≠ z := by intro h; subst i; dsimp [z] at hi; omega
          have hio : i ≠ o := by intro h; subst i; dsimp [o] at hi; omega
          exact ⟨hfix _ (a.injective.ne hiz) (a.injective.ne hio) (hab i z) (hab i o),
            hfix _ (hab z i).symm (hab o i).symm (b.injective.ne hiz) (b.injective.ne hio)⟩
        · intro x hxa hxb
          exact hfix x (hxa z) (hxa o) (hxb z) (hxb o)
      · have hprev : 2 ≤ d-1 := by omega
        obtain ⟨D,p,hp,hbD,hDa,hDb,hDlater,hDfix⟩ := ih (d-1) (by omega) hprev (by omega)
        let i : Fin m := ⟨d-1,by omega⟩
        have hiz : i ≠ z := by intro h; have := congrArg Fin.val h; dsimp [i,z] at this; omega
        have hio : i ≠ o := by intro h; have := congrArg Fin.val h; dsimp [i,o] at this; omega
        obtain ⟨C,q,hq,hbC,hCai,hCbi,hCaz,hCao,hCfix⟩ := exists_double_swap D hn
          (a i) (a z) (b i) (a o) (a.injective.ne hiz) (hab i i)
          (a.injective.ne hio) (hab z i) ha01 (hab o i).symm
          (nonzero_of_same_blank hbD (ha i)) (nonzero_of_same_blank hbD (ha z))
          (nonzero_of_same_blank hbD (hb i)) (nonzero_of_same_blank hbD (ha o))
        refine ⟨C,p.append q,?_,hbC.trans hbD,?_,?_,?_,?_⟩
        · rw [Path.length_append]
          have he : 6044*(d-1-1)*n + 6044*n = 6044*(d-1)*n := by
            have hdsub : d-1 = (d-1-1)+1 := by omega
            conv_rhs => rw [hdsub]
            ring
          exact (Nat.add_le_add hp hq).trans_eq he
        · intro j hj
          by_cases hji : j=i
          · subst j
            rw [hCai,(hDlater i (by rfl)).2]
            exact hQ i
          by_cases hjz : j=z
          · subst j
            rw [hCbi]
            exact hDa o (by dsimp [o]; omega)
          by_cases hjo : j=o
          · subst j
            rw [hCao]
            exact hDa z (by dsimp [z]; omega)
          rw [hCfix _ (a.injective.ne hji) (a.injective.ne hjz) (hab j i) (a.injective.ne hjo)]
          apply hDa
          have hne : j.val ≠ d-1 := by intro h; exact hji (Fin.ext h)
          omega
        · intro j hj
          by_cases hji : j=i
          · subst j
            rw [hCaz,(hDlater i (by rfl)).1]
            exact hP i
          rw [hCfix _ (hab i j).symm (hab z j).symm (b.injective.ne hji) (hab o j).symm]
          apply hDb
          have hne : j.val ≠ d-1 := by intro h; exact hji (Fin.ext h)
          omega
        · intro j hj
          have hji : j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i] at this; omega
          have hjz : j ≠ z := by intro h; have := congrArg Fin.val h; dsimp [z] at this; omega
          have hjo : j ≠ o := by intro h; have := congrArg Fin.val h; dsimp [o] at this; omega
          exact ⟨(hCfix _ (a.injective.ne hji) (a.injective.ne hjz) (hab j i)
            (a.injective.ne hjo)).trans (hDlater j (by omega)).1,
            (hCfix _ (hab i j).symm (hab z j).symm (b.injective.ne hji)
            (hab o j).symm).trans (hDlater j (by omega)).2⟩
        · intro x hxa hxb
          rw [hCfix x (hxa i) (hxa z) (hxb i) (hxa o),hDfix x hxa hxb]
  obtain ⟨C,p,hp,hbC,hCa,hCb,_,hfix⟩ := step m hm le_rfl
  refine ⟨C,p,?_,hbC,fun i => hCa i i.isLt,fun i => hCb i i.isLt,hfix⟩
  exact hp.trans (by gcongr; omega)

/-- The family exchange interface expressed directly with finite cell sets. -/
theorem exists_set_exchange (B : Board n) (hn : 4 ≤ n) (s t : Finset (Cell n))
    (hdis : Disjoint s t) (hcard : s.card = t.card) (hs : 2 ≤ s.card)
    (hs0 : ∀ x ∈ s, B x ≠ 0) (ht0 : ∀ x ∈ t, B x ≠ 0)
    (P Q : Tile n → Prop) (hP : ∀ x ∈ s, P (B x)) (hQ : ∀ x ∈ t, Q (B x)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 6044*s.card*n ∧ blank C = blank B ∧
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
  obtain ⟨C,p,hp,hb,hCa,hCb,hfix⟩ := exists_family_exchange B hn hs a b hab
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
