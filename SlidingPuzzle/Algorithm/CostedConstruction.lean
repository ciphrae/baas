import SlidingPuzzle.Algorithm.ParberryBounds

/-! Cost-function interfaces retain lower-order terms through the same legal
path constructions used by the uniform phase contracts. -/
namespace SlidingPuzzle
noncomputable section
open Classical

/-- A local solver whose full cost is retained. -/
def SolverCostBound (cost : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} [NeZero n], 8 ≤ n → ∀ B : ReachableBoard n,
    ∃ p : Path B.val (target n), p.length ≤ cost n

theorem parberrySolverCost : SolverCostBound (fun n => 5*n^3+1509*n^2+1505*n+4796) := by
  intro n _ hn B
  exact Parberry.exists_solution_cubic B (by omega)

section
variable {n m : ℕ} [NeZero n] [NeZero m]
theorem exists_solution_cubic_up_to_swap_of_cost {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (B : Board n) (hn : 8 ≤ n)
    (a b : Cell n) (hab : a ≠ b)
    (ha : target n a ≠ 0) (hb : target n b ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost n ∧ (C = target n ∨ C = swapCells (target n) a b) := by
  classical
  by_cases hreach : Reachable B
  · obtain ⟨p,hp⟩ := hsolver hn ⟨B,hreach⟩
    exact ⟨target n,p,hp,Or.inl rfl⟩
  let e : Equiv.Perm (Tile n) := Equiv.swap (target n a) (target n b)
  have he : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm
  have hsign : boardSign (relabel B e) = -boardSign B := by
    rw [relabel_swap]
    apply boardSign_swapCells
    intro h
    exact hab ((target n).injective (B.symm.injective h))
  have hparity : parityInvariant (relabel B e) = -parityInvariant B := by
    rw [parityInvariant,blank_relabel B e he,hsign]
    exact neg_mul _ _
  have hbad : parityInvariant B ≠ colorSign (blank (target n)) := by
    intro h
    exact hreach (reachable_of_parityInvariant (by omega) B h)
  have hgood : Reachable (relabel B e) := by
    apply reachable_of_parityInvariant (by omega)
    rw [hparity]
    rcases Int.units_eq_one_or (parityInvariant B) with h | h <;>
      rcases Int.units_eq_one_or (colorSign (blank (target n))) with ht | ht <;>
      simp_all
  obtain ⟨p,hp⟩ := hsolver hn ⟨relabel B e,hgood⟩
  have hes : e.symm 0 = 0 := by simpa [e] using he
  have hq : ∃ q : Path B (relabel (target n) e.symm), q.length ≤ cost n := by
    have h : ∃ q : Path (relabel (relabel B e) e.symm) (relabel (target n) e.symm),
        q.length ≤ cost n := ⟨p.relabel e.symm hes,by simpa using hp⟩
    rwa [relabel_relabel_symm] at h
  obtain ⟨q,hq⟩ := hq
  refine ⟨_,q,hq,Or.inr ?_⟩
  simp [e,relabel_swap]

theorem exists_borrowed_solution_of_cost {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (B T : Board n) (hm : 8 ≤ m)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (hcorner : B (blockEmbedding ro co hr hc (blank (target m))) =
      T (blockEmbedding ro co hr hc (blank (target m))))
    (a b : Cell m) (hab : a ≠ b) (ha : a ≠ blank (target m)) (hb' : b ≠ blank (target m)) :
    ∃ F : Board n, ∃ r : Path B F,
      r.length ≤ cost m+4*n ∧ blank F = blank B ∧
      ((∀ c, F (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc c)) ∨
       (∀ c, F (blockEmbedding ro co hr hc c) =
         T (blockEmbedding ro co hr hc (Equiv.swap a b c)))) ∧
      (∀ x, x ∉ Set.range (blockEmbedding ro co hr hc) → F x = B x) := by
  classical
  let ι := blockEmbedding ro co hr hc
  let z := blank (target m)
  let η := borrowedLabels ι T hzero
  obtain ⟨C,p,hp,hbC,hC⟩ := exists_block_corner_access B hb ro co hr hc
  have hCzero : C (ι z) = 0 := by rw [← hbC]; exact C.apply_symm_apply 0
  have hCη : ∀ c, C (ι c) ∈ Set.range η := by
    intro c
    by_cases hcz : c=z
    · subst c
      exact ⟨0,by simpa [η] using hCzero.symm⟩
    · obtain ⟨d,hd⟩ := hlabels c
      have hdz : d ≠ z := by
        intro he
        apply hcz
        apply ι.injective
        apply B.injective
        exact hd.trans (by rw [he]; exact hcorner.symm)
      exact ⟨target m d,by rw [borrowedLabels_target ι T hzero d hdz,hC c hcz]; exact hd.symm⟩
  obtain ⟨A,hA⟩ := exists_board_of_embedded_labels ι η C hCη
  have hAz : blank A = z := by
    apply ι.injective
    exact (blank_of_embedded_board ι η (borrowedLabels_zero _ _ _) A C hA).symm.trans hbC
  have hta : target m a ≠ 0 := by
    intro h
    exact ha ((target m).injective (h.trans ((target m).apply_symm_apply 0).symm))
  have htb : target m b ≠ 0 := by
    intro h
    exact hb' ((target m).injective (h.trans ((target m).apply_symm_apply 0).symm))
  obtain ⟨D,q,hq,hD⟩ := exists_solution_cubic_up_to_swap_of_cost hsolver A hm a b hab hta htb
  have hDz : blank D = z := by
    rcases hD with rfl | rfl
    · rfl
    · change Equiv.swap a b z = z
      exact Equiv.swap_apply_of_ne_of_ne ha.symm hb'.symm
  obtain ⟨E,s,hs,hE,hfix⟩ := q.exists_embedded ι
    (fun x y h => by rw [blockEmbedding_distance]; exact h) η (borrowedLabels_zero _ _ _) C hA
  have hbE : blank E = blank C := by
    rw [blank_of_embedded_board ι η (borrowedLabels_zero _ _ _) D E hE,hDz,hbC]
  let S : Set (Cell n) := {x | ∃ c, c ≠ z ∧ ι c=x}
  have haccess (x : Cell n) (hx : x ∈ S) : C x = B x := by
    obtain ⟨c,hc,rfl⟩ := hx
    exact hC c hc
  have hlocal (x : Cell n) (hx : x ∉ S) : E x = C x := by
    by_cases hin : x ∈ Set.range ι
    · obtain ⟨c,rfl⟩ := hin
      have he : c=z := by by_contra h; exact hx ⟨c,h,rfl⟩
      subst c
      have hez : E (ι z) = 0 := by rw [← hbC,← hbE]; exact E.apply_symm_apply 0
      exact hez.trans hCzero.symm
    · exact hfix x hin
  obtain ⟨F,r,hlen,hbF,hF,hFfix⟩ := p.exists_conjugated s hbE S haccess hlocal
  have hFcorner : F (ι z) = T (ι z) := by
    rw [hFfix]
    · exact hcorner
    · rintro ⟨c,hc,he⟩
      exact hc (ι.injective he)
  have hFn (c : Cell m) (hc : c ≠ z) : F (ι c) = η (D c) := by
    rw [hF _ ⟨c,hc,rfl⟩,hE]
  refine ⟨F,r,by omega,hbF,?_,?_⟩
  · rcases hD with rfl | rfl
    · left
      intro c
      by_cases hcz : c=z
      · subst c; exact hFcorner
      · rw [hFn c hcz,borrowedLabels_target ι T hzero c hcz]
    · right
      intro c
      have hswapz : Equiv.swap a b z=z := Equiv.swap_apply_of_ne_of_ne ha.symm hb'.symm
      by_cases hcz : c=z
      · subst c; rw [hswapz]; exact hFcorner
      · have hsc : Equiv.swap a b c ≠ z := by
          intro he
          exact hcz ((Equiv.swap a b).injective (he.trans hswapz.symm))
        rw [hFn c hcz]
        exact borrowedLabels_target ι T hzero (Equiv.swap a b c) hsc
  · intro x hx
    apply hFfix
    rintro ⟨c,_,he⟩
    exact hx ⟨c,he⟩

theorem exists_block_finish_of_cost {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (B T : Board n) (hm : 8 ≤ m) (hn : 4 ≤ n)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (u v : Cell n) (huv : u ≠ v)
    (hu : u ∉ Set.range (blockEmbedding ro co hr hc))
    (hv : v ∉ Set.range (blockEmbedding ro co hr hc))
    (hu0 : B u ≠ 0) (hv0 : B v ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost m+9352*n ∧ blank C = blank B ∧
      (∀ c, C (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc c)) ∧
      ((C u = B u ∧ C v = B v) ∨ (C u = B v ∧ C v = B u)) ∧
      (∀ x, x ∉ Set.range (blockEmbedding ro co hr hc) → x ≠ u → x ≠ v → C x = B x) := by
  classical
  let ι := blockEmbedding ro co hr hc
  let z := blank (target m)
  let a : Cell m := (0,0)
  let b : Cell m := (0,⟨1,by omega⟩)
  have haz : a ≠ z := by
    intro h
    have hh := congrArg (fun x : Cell m => x.1.val) h
    dsimp [z] at hh
    rw [blank_target_eq] at hh
    change 0=m-1 at hh
    omega
  have hbz : b ≠ z := by
    intro h
    have hh := congrArg (fun x : Cell m => x.1.val) h
    dsimp [z] at hh
    rw [blank_target_eq] at hh
    change 0=m-1 at hh
    omega
  have hab : a ≠ b := by simp [a,b,Fin.ext_iff]
  obtain ⟨D,p,hp,hbD,hDz,hDlabels,hDfix⟩ := exists_correct_block_corner B T hn ι z a b
    haz.symm hbz.symm hab hzero hlabels
  obtain ⟨E,q,hq,hbE,hE,hEfix⟩ := exists_borrowed_solution_of_cost hsolver D T hm ro co hr hc
    (hbD.trans hb) hzero hDlabels hDz a b hab haz hbz
  have hout (x : Cell n) (hx : x ∉ Set.range ι) : E x = B x :=
    (hEfix x hx).trans (hDfix x hx)
  have hEu : E u=B u := hout u hu
  have hEv : E v=B v := hout v hv
  rcases hE with hE | hE
  · refine ⟨E,p.append q,?_,hbE.trans hbD,hE,Or.inl ⟨hEu,hEv⟩,?_⟩
    · rw [Path.length_append]; omega
    · intro x hx _ _; exact hout x hx
  · have hau : ι a ≠ u := fun h => hu ⟨a,h⟩
    have hav : ι a ≠ v := fun h => hv ⟨a,h⟩
    have hbu : ι b ≠ u := fun h => hu ⟨b,h⟩
    have hbv : ι b ≠ v := fun h => hv ⟨b,h⟩
    have hEa : E (ι a)=T (ι b) := by simpa using hE a
    have hEb : E (ι b)=T (ι a) := by simpa using hE b
    obtain ⟨C,s,hs,hbC,hCa,hCu,hCb,hCv,hfix⟩ := exists_double_swap E hn
      (ι a) u (ι b) v hau (ι.injective.ne hab) hav hbu.symm huv hbv
      (by rw [hEa]; exact hzero b) (by rwa [hEu])
      (by rw [hEb]; exact hzero a) (by rwa [hEv])
    refine ⟨C,(p.append q).append s,?_,hbC.trans (hbE.trans hbD),?_,
      Or.inr ⟨hCu.trans hEv,hCv.trans hEu⟩,?_⟩
    · simp only [Path.length_append]; omega
    · intro c
      by_cases hca : c=a
      · subst c; exact hCa.trans hEb
      by_cases hcb : c=b
      · subst c; exact hCb.trans hEa
      rw [hfix _ (ι.injective.ne hca) (fun h => hu ⟨c,h⟩)
        (ι.injective.ne hcb) (fun h => hv ⟨c,h⟩),hE,
        Equiv.swap_apply_of_ne_of_ne hca hcb]
    · intro x hx hxu hxv
      rw [hfix x (fun h => hx ⟨a,h.symm⟩) hxu (fun h => hx ⟨b,h.symm⟩) hxv]
      exact hout x hx

end
namespace Partition
section
variable {k : ℕ} [NeZero (k^4)]
theorem exists_finish_one_square_of_cost {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk)
    (u v : Cell (k^4)) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target (k^4))) (hv0 : v ≠ blank (target (k^4))) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ cost (k^3)+9352*k^4 ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      (∀ x, square i x → C x = target (k^4) x) ∧
      (∀ (j : GroupIndex k), j ≠ i → j ≠ lastGroup k hk →
        ∀ x, square j x → C x = B x) := by
  classical
  let : NeZero (k^3) := ⟨by positivity⟩
  have hm : 8 ≤ k^3 := by nlinarith [Nat.pow_le_pow_left hk 3]
  have hn : 4 ≤ k^4 := by nlinarith [Nat.pow_le_pow_left hk 4]
  have hBu : B u ≠ 0 := by
    intro h
    exact hu0 ((B.injective (h.trans (B.apply_symm_apply 0).symm)).trans hb)
  have hBv : B v ≠ 0 := by
    intro h
    exact hv0 ((B.injective (h.trans (B.apply_symm_apply 0).symm)).trans hb)
  have huout : u ∉ Set.range (squareEmbedding i) := by
    intro h
    exact hi (square_unique hk ((mem_range_squareEmbedding hk i u).mp h) hu)
  have hvout : v ∉ Set.range (squareEmbedding i) := by
    intro h
    exact hi (square_unique hk ((mem_range_squareEmbedding hk i v).mp h) hv)
  obtain ⟨C,p,hp,hbC,hC,hbuf,hfix⟩ := exists_block_finish_of_cost hsolver B (target (k^4)) hm hn
    ((groupRow i).val*k^3) ((groupCol i).val*k^3)
    (by simpa [Nat.add_mul] using square_block_end (groupRow i))
    (by simpa [Nat.add_mul] using square_block_end (groupCol i)) hb
    (squareEmbedding_target_nonzero hk i hi) (squaresSorted_block_labels hk B hB hb i hi)
    u v huv huout hvout hBu hBv
  have hsolved (x : Cell (k^4)) (hx : square i x) : C x=target (k^4) x := by
    obtain ⟨c,rfl⟩ := (mem_range_squareEmbedding hk i x).mpr hx
    exact hC c
  have hCu : C u ∈ targetGroup (lastGroup k hk) := by
    rcases hbuf with h | h
    · rw [h.1]; exact hB _ u hu (fun hz => hBu (Fin.ext hz))
    · rw [h.1]; exact hB _ v hv (fun hz => hBv (Fin.ext hz))
  have hCv : C v ∈ targetGroup (lastGroup k hk) := by
    rcases hbuf with h | h
    · rw [h.2]; exact hB _ v hv (fun hz => hBv (Fin.ext hz))
    · rw [h.2]; exact hB _ u hu (fun hz => hBu (Fin.ext hz))
  refine ⟨C,p,?_,hbC,?_,hsolved,?_⟩
  · simpa [← pow_mul] using hp
  · intro j x hx hnonzero
    by_cases hxi : square i x
    · rw [hsolved x hxi] at hnonzero ⊢
      exact (mem_targetGroup j _).mpr ⟨hnonzero,by simpa [position] using hx⟩
    by_cases hxu : x=u
    · subst x
      have he : j=lastGroup k hk := square_unique hk hx hu
      rwa [he]
    by_cases hxv : x=v
    · subst x
      have he : j=lastGroup k hk := square_unique hk hx hv
      rwa [he]
    have hnot : x ∉ Set.range (squareEmbedding i) :=
      fun h => hxi ((mem_range_squareEmbedding hk i x).mp h)
    rw [hfix x hnot hxu hxv] at hnonzero ⊢
    exact hB j x hx hnonzero
  · intro j hji hjlast x hx
    apply hfix
    · intro h
      exact hji (square_unique hk hx ((mem_range_squareEmbedding hk i x).mp h))
    · intro he
      subst x
      exact hjlast (square_unique hk hx hu)
    · intro he
      subst x
      exact hjlast (square_unique hk hx hv)

theorem exists_finish_square_schedule_of_cost {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (u v : Cell (k^4)) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target (k^4))) (hv0 : v ≠ blank (target (k^4))) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (k*k-1)*(cost (k^3)+9352*k^4) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k), i ≠ lastGroup k hk → ∀ x, square i x → C x = target (k^4) x := by
  classical
  have schedule (s : Finset (GroupIndex k)) (hs : lastGroup k hk ∉ s) :
      ∃ C : Board (k^4), ∃ p : Path B C,
        p.length ≤ s.card*(cost (k^3)+9352*k^4) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
        ∀ i ∈ s, ∀ x, square i x → C x=target (k^4) x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨B,Path.nil B,by simp,rfl,hB,by simp⟩
    | @insert i s his ih =>
      have hilast : i ≠ lastGroup k hk := by intro h; subst i; simp at hs
      have hslast : lastGroup k hk ∉ s := fun h => hs (Finset.mem_insert_of_mem h)
      obtain ⟨D,p,hp,hbD,hD,hsolved⟩ := ih hslast
      obtain ⟨C,q,hq,hbC,hC,hCi,hfix⟩ := exists_finish_one_square_of_cost hsolver hk D hD (hbD.trans hb)
        i hilast u v huv hu hv hu0 hv0
      refine ⟨C,p.append q,?_,hbC.trans hbD,hC,?_⟩
      · rw [Path.length_append,Finset.card_insert_of_notMem his]
        calc
          p.length+q.length ≤ s.card*(cost (k^3)+9352*k^4)+(cost (k^3)+9352*k^4) :=
            Nat.add_le_add hp hq
          _ = (s.card+1)*(cost (k^3)+9352*k^4) := by ring
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hCi x hx
        · have hji : j ≠ i := fun h => his (h ▸ hj)
          have hjlast : j ≠ lastGroup k hk := fun h => hslast (h ▸ hj)
          rw [hfix j hji hjlast x hx]
          exact hsolved j hj x hx
  obtain ⟨C,p,hp,hbC,hC,hsolved⟩ := schedule (Finset.univ.erase (lastGroup k hk)) (by simp)
  refine ⟨C,p,?_,hbC,hC,?_⟩
  · simpa using hp
  · intro i hi x hx
    exact hsolved i (by simp [hi]) x hx

theorem exists_finish_path_of_cost {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (hk : 2 ≤ k) (B : Board (k^4)) (hB : Arranged hk B) :
    ∃ p : Path B (target (k^4)), p.length ≤ k^2*cost (k^3)+9354*k^6 := by
  let : NeZero (k^3) := ⟨by positivity⟩
  have hm : 8 ≤ k^3 := by nlinarith [Nat.pow_le_pow_left hk 3]
  obtain ⟨A,p,hp,hbA,hA⟩ := exists_finish_blank_access hk B hB.sorted hB.blank_last
  obtain ⟨u,v,huv,hu,hv,hu0,hv0⟩ := exists_finish_buffers hk
  obtain ⟨D,q,hq,hbD,hD,hsolved⟩ := exists_finish_square_schedule_of_cost hsolver hk A hA hbA
    u v huv hu hv hu0 hv0
  let d := (k-1)*k^3
  have hd : d+k^3=k^4 := by
    dsimp [d]
    have h := Nat.sub_add_cancel (by omega : 1 ≤ k)
    calc
      (k-1)*k^3+k^3 = (k-1+1)*k^3 := by ring
      _ = k^4 := by rw [h]; ring
  have hprefix : ∀ x y : Fin (k^4), x.val<d ∨ y.val<d → D (x,y)=target (k^4) (x,y) := by
    intro x y hxy
    obtain ⟨i,hi⟩ := square_covers hk rfl (x,y)
    apply hsolved i _ (x,y) hi
    intro he
    rw [he] at hi
    simp only [square,lastGroup,groupRow,groupCol,Equiv.symm_apply_apply] at hi
    dsimp [d] at hxy
    omega
  have hreach : Reachable D := by
    obtain ⟨r⟩ := hB.reachable
    exact ⟨(r.append p).append q⟩
  obtain ⟨R,hR⟩ := exists_residual_board d hd D hprefix
  have hrR : Reachable R := residual_reachable (by omega) d hd D hprefix R hR hreach
  obtain ⟨r,hr⟩ := hsolver hm ⟨R,hrR⟩
  obtain ⟨s,hs⟩ := residual_solution_lifts d hd D hprefix R hR r
  refine ⟨(p.append q).append s,?_⟩
  simp only [Path.length_append,hs]
  have hcount : k*k-1+1 = k*k := Nat.sub_add_cancel (by nlinarith)
  have htotal : q.length+r.length ≤ k^2*cost (k^3)+9352*(k*k-1)*k^4 := by
    calc
      q.length+r.length ≤ (k*k-1)*(cost (k^3)+9352*k^4)+cost (k^3) :=
        Nat.add_le_add hq hr
      _ = (k*k-1+1)*cost (k^3)+9352*(k*k-1)*k^4 := by ring
      _ = k^2*cost (k^3)+9352*(k*k-1)*k^4 := by rw [hcount]; ring
  have hsub := Nat.mul_le_mul_right (k^4) (Nat.sub_le (k*k) 1)
  have h46 : k^4 ≤ k^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp' : p.length ≤ 2*k^4 := hp
  nlinarith

/-- A staging construction: all compressed quotas and representatives are
filled, with the blank below row `k²` and right of column `k³`. The length bound
is doubled so that half-integer leading coefficients are retained. -/
def RepresentativeStaging {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)] (L : ℕ) : Prop :=
  ∀ B : Board (k^4), ∃ C : Board (k^4), ∃ p : Path B C,
    2*p.length ≤ L ∧
    (∀ (i : GroupIndex k) (c : Cell (k^4)),
      c ∈ stagingCells i → C c ∈ targetGroup i) ∧
    (∀ i : GroupIndex k, i ≠ lastGroup k hk →
      C (representativeSource hk i) ∈ targetGroup i) ∧
    k^2+1 ≤ (blank C).1.val ∧ k^3 ≤ (blank C).2.val

theorem exists_staging_representative_row_path_with_blank_of_cost {k : ℕ}
    (hk : 2 ≤ k) [NeZero (k^4)] {L : ℕ} (hstaging : RepresentativeStaging hk L)
    (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      2*p.length ≤ L+18*k^6 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)),
        c ∈ stagingCells i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk →
        C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).1.val = k^4-1 ∧ (blank C).2.val = k^4-k^2 := by
  have hg := preparation_geometry hk
  have hk2 : 1 < k^2 := by nlinarith
  obtain ⟨A,p,hp,hstage,hrep,hbr,hbc⟩ := hstaging B
  let access : Cell (k^4) :=
    (⟨k^2+2,by omega⟩,⟨k^4-k^2,by omega⟩)
  obtain ⟨D,q,hblank,hq,hfix⟩ := exists_blank_access_path_preserving A access
  have hqstage (i : GroupIndex k) (c : Cell (k^4)) (hc : c ∈ stagingCells i) :
      D c = A c := by
    apply hfix
    rcases stagingCells_compressed hk hc with hr | hcol
    · left
      change c.1.val < min (blank A).1.val (k^2+2)
      exact lt_min (by omega) (by omega)
    · right; right; left
      change c.2.val < min (blank A).2.val (k^4-k^2)
      exact lt_min (by omega) (by omega)
  have hqrep (i : GroupIndex k) : D (representativeSource hk i) = A (representativeSource hk i) := by
    apply hfix
    left
    change k^2 < min (blank A).1.val (k^2+2)
    exact lt_min (by omega) (by omega)
  obtain ⟨E,s,hs,hrow,hsfix,hsblank⟩ := exists_row_translation_with_blank D (k^2) (k^4-k^2)
    (k^2) (k^4-3-k^2) (by omega) (by omega) hk2 hblank
  have hEstage (i : GroupIndex k) (c : Cell (k^4)) (hc : c ∈ stagingCells i) :
      E c ∈ targetGroup i := by
    rw [hsfix c, hqstage i c hc]
    · exact hstage i c hc
    · rcases stagingCells_compressed hk hc with hr | hcol
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inl (by omega)))
  have hErep (i : GroupIndex k) (hi : i ≠ lastGroup k hk) :
      E (⟨k^4-3,by omega⟩,(representativeSource hk i).2) ∈ targetGroup i := by
    have hil : i.val < k^2 := by simpa [pow_two] using i.isLt
    have hh := hrow ⟨i.val,hil⟩
    have hroweq : k^2 + (k^4-3-k^2) = k^4-3 := by omega
    simp only [hroweq] at hh
    change E (⟨k^4-3,by omega⟩,(representativeSource hk i).2) =
      D (representativeSource hk i) at hh
    rw [hh,hqrep]
    exact hrep i hi
  refine ⟨E,(p.append q).append s,?_,hEstage,hErep,?_⟩
  · have hqbound : q.length ≤ 2*k^4 := by
      apply hq.trans
      unfold gridDistance Nat.dist
      have := (blank A).1.isLt
      have := (blank A).2.isLt
      have := access.1.isLt
      have := access.2.isLt
      omega
    have hsbound : s.length ≤ 7*k^6 := by
      calc
        s.length ≤ (k^4-3-k^2)*(6*k^2+3) := hs
        _ ≤ k^4*(7*k^2) := Nat.mul_le_mul (by omega) (by nlinarith)
        _ = 7*k^6 := by ring
    have h46 : k^4 ≤ k^6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h611 : k^6 ≤ k^11 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Path.length_append]
    nlinarith [Nat.mul_le_mul_left 2 h611, Nat.mul_le_mul_left 7 h611]
  · rw [hsblank]
    change k^2+(k^4-3-k^2)+2 = k^4-1 ∧ k^4-k^2 = k^4-k^2
    omega

theorem exists_horizontal_prepared_path_with_blank_of_cost {k : ℕ}
    (hk : 2 ≤ k) [NeZero (k^4)] {L : ℕ} (hstaging : RepresentativeStaging hk L)
    (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      2*p.length ≤ L+18*k^6+24*k^10 ∧ (blank C).1.val = k^4-1 ∧
      (∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → C c ∈ targetGroup i) ∧
      (∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → C c ∈ targetGroup i) ∧
      (∀ i : GroupIndex k, i ≠ lastGroup k hk → C (representativeDestination hk i) ∈ targetGroup i) ∧
      (blank C).2.val = k^4-k^2 := by
  obtain ⟨A,p,hp,hstage,hrep,hbr,hbc⟩ := exists_staging_representative_row_path_with_blank_of_cost hk hstaging B
  obtain ⟨C,q,hq,hb,hH,hCs,hR⟩ := exists_horizontal_preparation_path hk A hstage hbr
  refine ⟨C,p.append q,?_,by rw [hb]; exact hbr,hH,?_,?_,by rw [hb]; exact hbc⟩
  · rw [Path.length_append]
    omega
  · intro j i c hc
    rw [hCs j i c hc]
    exact hstage i c ((mem_stagingCells i c).mpr (Or.inr (Or.inr ⟨j,hc⟩)))
  · intro i hi
    rw [hR]
    exact hrep i hi

/-- Column `i` of a band needs only `i/k²` chunks; pairing `i` with `k³-1-i`
bounds the total number of chunks by `k³(k-1)/2`. -/
theorem sum_div_sq_le {k : ℕ} (hk : 2 ≤ k) :
    2*(∑ i ∈ Finset.range (k^3), i/k^2)+k^3 ≤ k^4 := by
  have hk2 : 0 < k^2 := by positivity
  have hrefl := Finset.sum_range_reflect (fun i => i/k^2) (k^3)
  have hpair : ∑ i ∈ Finset.range (k^3), (i/k^2+(k^3-1-i)/k^2) ≤
      ∑ _i ∈ Finset.range (k^3), (k-1) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    calc
      i/k^2+(k^3-1-i)/k^2 ≤ (i+(k^3-1-i))/k^2 := Nat.add_div_le_add_div _ _ _
      _ = (k^3-1)/k^2 := by congr 1; omega
      _ ≤ k-1 := by
        apply Nat.le_sub_one_of_lt
        apply (Nat.div_lt_iff_lt_mul hk2).mpr
        have : k*k^2 = k^3 := by ring
        omega
  rw [Finset.sum_add_distrib, hrefl, Finset.sum_const, Finset.card_range, smul_eq_mul] at hpair
  have hk3 : k^3*(k-1)+k^3 = k^4 := by
    have h := Nat.sub_add_cancel (by omega : 1 ≤ k)
    calc
      k^3*(k-1)+k^3 = k^3*(k-1+1) := by ring
      _ = k^4 := by rw [h]; ring
  omega

theorem exists_vertical_band_path_cost {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (a : ℕ) (ha : a < k)
    (hb : (blank B).2.val = k^4-k^2) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      2*p.length ≤ 8*k^10 ∧ blank C = blank B ∧
      (∀ (r : Fin (k^4)) (c : Fin (k^3)),
        a*k^3+k ≤ r.val → r.val < (a+1)*k^3 →
        C (r,⟨verticalDestination k c.val,by have := verticalDestination_bounds hk c.val c.isLt; omega⟩) =
        B (r,⟨c.val,by have := vertical_geometry hk; have := c.isLt; omega⟩)) ∧
      (∀ x : Cell (k^4), ¬ verticalPreparationBand k a x ∨ k^4-k^2 ≤ x.2.val → C x = B x) := by
  have hg := vertical_geometry hk
  have hblock : (a+1)*k^3 ≤ k^4 := by
    calc
      (a+1)*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ ha
      _ = k^4 := by ring
  have hrows : a*k^3+k+(k^3-k) = (a+1)*k^3 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  obtain ⟨C,p,hp,hbC,hcol,hfix⟩ := exists_descending_column_schedule_var B (a*k^3+k)
    (k^3-k) (k^3) (k^3) (fun i => i/k^2) (by omega) (by omega) (by omega)
    (verticalDestination k) (verticalDestination_strictMono hk) (by
      intro i hi
      have hh := verticalDestination_bounds hk i hi
      rw [hb]
      refine ⟨hh.1,hh.2.2,hh.2.1,?_⟩
      have hid := Nat.div_add_mod' i (k^2)
      have hmul := Nat.mul_le_mul_left (i/k^2) (show k^2 ≤ k^3 by omega)
      unfold verticalDestination
      omega)
  refine ⟨C,p,?_,hbC,?_,?_⟩
  · have hsum := sum_div_sq_le hk
    set s := ∑ i ∈ Finset.range (k^3), i/k^2
    have hW : 4*k^4+k^3*(2*k^3+6*(k^3-k)+8) ≤ 8*k^6+4*k^4+8*k^3 := by
      have h1 : 2*k^3+6*(k^3-k)+8 ≤ 8*k^3+8 := by omega
      have h2 := Nat.mul_le_mul_left (k^3) h1
      have h3 : k^3*(8*k^3+8) = 8*k^6+8*k^3 := by ring
      omega
    have hlen : p.length ≤ s*(8*k^6+4*k^4+8*k^3) := hp.trans (Nat.mul_le_mul_left s hW)
    have hmul := Nat.mul_le_mul_right (8*k^6+4*k^4+8*k^3) hsum
    have h89 : 2*k^8 ≤ k^9 := by
      have := Nat.mul_le_mul_left (k^8) hk; nlinarith [show k^8*k = k^9 by ring]
    have h79 : 4*k^7 ≤ k^9 := by
      have := Nat.mul_le_mul_left (k^7) (Nat.pow_le_pow_left hk 2)
      nlinarith [show k^7*k^2 = k^9 by ring]
    have he1 : (2*s+k^3)*(8*k^6+4*k^4+8*k^3) =
        2*(s*(8*k^6+4*k^4+8*k^3))+(8*k^9+4*k^7+8*k^6) := by ring
    have he2 : k^4*(8*k^6+4*k^4+8*k^3) = 8*k^10+4*k^8+8*k^7 := by ring
    omega
  · intro r c hrlo hrhi
    let j : Fin (k^3-k) := ⟨r.val-(a*k^3+k),by omega⟩
    have hh := hcol c.val c.isLt j
    have he : (⟨a*k^3+k+j.val,by omega⟩ : Fin (k^4)) = r := by
      apply Fin.ext
      change a*k^3+k+(r.val-(a*k^3+k)) = r.val
      omega
    simpa only [he] using hh
  · intro x hx
    apply hfix
    rcases hx with hx | hx
    · unfold verticalPreparationBand at hx
      omega
    · right; right
      intro i hi
      have hh := verticalDestination_bounds hk i hi
      omega

theorem exists_vertical_spread_prefix_cost {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (R : ℕ) (hR : R ≤ k)
    (hb : (blank B).2.val = k^4-k^2) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      2*p.length ≤ R*(8*k^10) ∧ blank C = blank B ∧
      (∀ (a : ℕ) (ha : a < R) (r : Fin (k^4)) (c : Fin (k^3)),
        a*k^3+k ≤ r.val → r.val < (a+1)*k^3 →
        C (r,⟨verticalDestination k c.val,by have := verticalDestination_bounds hk c.val c.isLt; omega⟩) =
        B (r,⟨c.val,by have := vertical_geometry hk; have := c.isLt; omega⟩)) ∧
      (∀ x : Cell (k^4), (∀ a < R, ¬ verticalPreparationBand k a x) ∨
        k^4-k^2 ≤ x.2.val → C x = B x) := by
  induction R with
  | zero =>
    refine ⟨B,Path.nil B,by simp,rfl,?_,fun _ _ => rfl⟩
    intro a ha
    omega
  | succ R ih =>
    obtain ⟨D,p,hp,hbD,hcolsD,hfixD⟩ := ih (by omega)
    obtain ⟨E,q,hq,hbE,hcolsE,hfixE⟩ := exists_vertical_band_path_cost hk D R (by omega) (by rw [hbD]; exact hb)
    refine ⟨E,p.append q,?_,hbE.trans hbD,?_,?_⟩
    · rw [Path.length_append]
      have : (R+1)*(8*k^10) = R*(8*k^10)+8*k^10 := by ring
      omega
    · intro a ha r c hrlo hrhi
      by_cases har : a < R
      · rw [hfixE _ (Or.inl (by
          intro hh
          have he := verticalPreparationBand_unique (show verticalPreparationBand k a _ from ⟨hrlo,hrhi⟩) hh
          omega))]
        exact hcolsD a har r c hrlo hrhi
      · have he : a = R := by omega
        subst a
        rw [hcolsE r c hrlo hrhi]
        apply hfixD
        left
        intro a ha hh
        have he := verticalPreparationBand_unique hh (show verticalPreparationBand k R _ from ⟨hrlo,hrhi⟩)
        omega
    · intro x hx
      rw [hfixE x (by
        rcases hx with hx | hx
        · exact Or.inl (hx R (by omega))
        · exact Or.inr hx)]
      apply hfixD
      rcases hx with hx | hx
      · exact Or.inl (fun a ha => hx a (by omega))
      · exact Or.inr hx

theorem exists_vertical_preparation_path_cost {k : ℕ} (hk : 2 ≤ k) [NeZero (k^4)]
    (B : Board (k^4)) (hb : (blank B).2.val = k^4-k^2)
    (hH : ∀ (i : GroupIndex k) (c : Cell (k^4)), horizontal i c → B c ∈ targetGroup i)
    (hV : ∀ (j i : GroupIndex k) (c : Cell (k^4)), c ∈ stagingC j i → B c ∈ targetGroup i) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      2*p.length ≤ 8*k^11 ∧ Clear (k := k) C ∧
      (∀ i : GroupIndex k, C (representativeDestination hk i) = B (representativeDestination hk i)) := by
  have hg := vertical_geometry hk
  obtain ⟨C,p,hp,hbC,hcols,hfix⟩ := exists_vertical_spread_prefix_cost hk B k le_rfl hb
  refine ⟨C,p,?_,⟨?_,?_⟩,?_⟩
  · calc
      2*p.length ≤ k*(8*k^10) := hp
      _ = 8*k^11 := by ring
  · intro i c hc
    rw [hfix c (Or.inl (by
      intro a ha hh
      have hmod := horizontal_mod hk hc
      have hdiv : c.1.val/k^3 = a := Nat.div_eq_of_lt_le (by have := hh.1; omega) hh.2
      have he := Nat.div_add_mod' c.1.val (k^3)
      rw [hdiv] at he
      have := hh.1
      omega))]
    exact hH i c hc
  · intro j i c hc
    have hi : i.val < k^2 := by simpa [pow_two] using i.isLt
    have hcol := (groupCol j).isLt
    have hsource : (groupCol j).val*k^2+i.val < k^3 := by
      have hh := Nat.mul_le_mul_right (k^2) hcol
      have he : k*k^2 = k^3 := by ring
      nlinarith
    let s : Fin (k^3) := ⟨(groupCol j).val*k^2+i.val,hsource⟩
    have hd : verticalDestination k s.val = (groupCol j).val*k^3+i.val := by
      unfold verticalDestination
      dsimp [s]
      have hdiv : ((groupCol j).val*k^2+i.val)/k^2 = (groupCol j).val := by
        apply Nat.div_eq_of_lt_le
        · omega
        · rw [Nat.add_mul, Nat.one_mul]
          omega
      rw [hdiv]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
    have hh := hcols (groupRow j).val (groupRow j).isLt c.1 s hc.1 hc.2.1
    have he : (⟨verticalDestination k s.val,by have := verticalDestination_bounds hk s.val s.isLt; omega⟩ : Fin (k^4)) = c.2 :=
      Fin.ext (hd.trans hc.2.2.symm)
    rw [he] at hh
    rw [hh]
    apply hV j i
    exact (mem_stagingC j i _).mpr ⟨hc.1,hc.2.1,rfl⟩
  · intro i
    apply hfix
    right
    change k^4-k^2 ≤ k^4-k^2+i.val
    omega

theorem exists_preparation_path_of_cost {k : ℕ}
    (hk : 2 ≤ k) [NeZero (k^4)] {L : ℕ} (hstaging : RepresentativeStaging hk L)
    (B : Board (k^4)) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      2*p.length ≤ L+18*k^6+24*k^10+8*k^11 ∧ Clear (k := k) C ∧ LastRepresentatives hk C := by
  classical
  obtain ⟨A,p,hp,_,hH,hV,hR,hb⟩ := exists_horizontal_prepared_path_with_blank_of_cost hk hstaging B
  obtain ⟨C,q,hq,hclear,hfix⟩ := exists_vertical_preparation_path_cost hk A hb hH hV
  refine ⟨C,p.append q,?_,hclear,?_⟩
  · rw [Path.length_append]
    nlinarith
  · intro i hi
    have hc : representativeDestination hk i ∈ reservoirCells (lastGroup k hk) := by
      simpa only [mem_reservoirCells] using representative_destination_in_last_reservoir hk i
    have hmem : C (representativeDestination hk i) ∈ targetGroup i := by
      rw [hfix]
      exact hR i hi
    unfold reservoirCount
    have hh := Finset.single_le_sum (f := fun x : Cell (k^4) =>
      if C x ∈ targetGroup i then 1 else 0) (fun _ _ => Nat.zero_le _) hc
    rw [if_pos hmem] at hh
    omega

theorem exists_arrangement_path_cost (hk : 2 ≤ k) (B : Board (k^4))
    (hclear : Clear (k := k) B) (hsorted : ReservoirSorted (k := k) B) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (24*(k^3-k)+2032)*(k^4-k^2)*k^4 + (24*k^3+2032)*(k^3-k^2)*k^4 ∧ blank C = blank B ∧
      SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k) x, reservoir i x → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDV,hDH,hDR⟩ := exists_vertical_arrangement_path hk B hclear
  have hH : ∀ (i : GroupIndex k) x, horizontal i x → D x ∈ targetGroup i := by
    intro i x hx
    rw [hDH i x hx]
    exact hclear.1 i x hx
  obtain ⟨C,q,hq,hbC,hCH,hCV,hCR⟩ := exists_horizontal_arrangement_path hk D hH
  have hR (i : GroupIndex k) (x : Cell (k^4)) (hx : reservoir i x) : C x = B x :=
    (hCR i x hx).trans (hDR i x hx)
  refine ⟨C,p.append q,?_,hbC.trans hbD,?_,hR⟩
  · rw [Path.length_append]
    exact Nat.add_le_add hp hq
  · intro i x hxi hnonzero
    rcases covers hk rfl x with ⟨j,hxH⟩ | ⟨j,l,hxV⟩ | ⟨j,hxR⟩
    · let a : SliceIndex k := (j,groupCol i)
      have hxa : x ∈ horizontalSliceCells a.1 a.2 := by
        apply (mem_horizontalSliceCells _ _ _).mpr
        exact ⟨hxH,hxi.2.2⟩
      have he : sliceDestination a = i :=
        square_unique hk (horizontalSlice_subset_square hk a hxa) hxi
      rw [← he]
      exact hCH a x hxa
    · have he : j=i := square_unique hk (vertical_subset_square hk hxV) hxi
      rw [hCV j l x hxV,← he]
      exact hDV j l x hxV
    · have he : j=i := square_unique hk (reservoir_subset_square hxR) hxi
      rw [hR j x hxR,← he]
      apply hsorted j x hxR
      rwa [hR j x hxR] at hnonzero

end
end Partition
end
end SlidingPuzzle
