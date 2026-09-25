import SlidingPuzzle.Moves.Exchange
import SlidingPuzzle.Parberry.Solver
import SlidingPuzzle.Moves.LocalSolve
import SlidingPuzzle.Algorithm.Finish.Access
import SlidingPuzzle.Moves.BorrowedSolve
import SlidingPuzzle.Moves.BlockCorner

/-! Phase IV (Finish). Each square of side `side n k` is solved by a local solver, with
parity repaired by borrowing a tile, and the last square is solved in place.
The local solver is abstract (`SolverCostBound`); the constructed Parberry-style
solver supplies `5*n³+O(n²)`. -/
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
theorem exists_solution_cubic_up_to_swap {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
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

theorem exists_borrowed_solution {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
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
  obtain ⟨D,q,hq,hD⟩ := exists_solution_cubic_up_to_swap hsolver A hm a b hab hta htb
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

theorem exists_block_finish {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
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
  obtain ⟨E,q,hq,hbE,hE,hEfix⟩ := exists_borrowed_solution hsolver D T hm ro co hr hc
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
variable {n k : ℕ} [NeZero n]
theorem exists_finish_one_square {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (hk : Dims n k) (B : Board n)
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target n))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk)
    (u v : Cell n) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target n)) (hv0 : v ≠ blank (target n)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost (side n k)+9352*n ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      (∀ x, square i x → C x = target n x) ∧
      (∀ (j : GroupIndex k), j ≠ i → j ≠ lastGroup k hk →
        ∀ x, square j x → C x = B x) := by
  classical
  let : NeZero (side n k) := ⟨hk.side_pos.ne'⟩
  have hm : 8 ≤ side n k := by have := hk.cube_le; have := Nat.pow_le_pow_left hk.two_le 3; omega
  have hn : 4 ≤ n := hk.two_le_n
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
  obtain ⟨C,p,hp,hbC,hC,hbuf,hfix⟩ := exists_block_finish hsolver B (target n) hm hn
    ((groupRow i).val*side n k) ((groupCol i).val*side n k)
    (by simpa [Nat.add_mul] using square_block_end (n := n) (groupRow i))
    (by simpa [Nat.add_mul] using square_block_end (n := n) (groupCol i)) hb
    (squareEmbedding_target_nonzero hk i hi) (squaresSorted_block_labels hk B hB hb i hi)
    u v huv huout hvout hBu hBv
  have hsolved (x : Cell n) (hx : square i x) : C x=target n x := by
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

theorem exists_finish_square_schedule {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (hk : Dims n k) (B : Board n)
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target n))
    (u v : Cell n) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target n)) (hv0 : v ≠ blank (target n)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (k*k-1)*(cost (side n k)+9352*n) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k), i ≠ lastGroup k hk → ∀ x, square i x → C x = target n x := by
  classical
  have schedule (s : Finset (GroupIndex k)) (hs : lastGroup k hk ∉ s) :
      ∃ C : Board n, ∃ p : Path B C,
        p.length ≤ s.card*(cost (side n k)+9352*n) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
        ∀ i ∈ s, ∀ x, square i x → C x=target n x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨B,Path.nil B,by simp,rfl,hB,by simp⟩
    | @insert i s his ih =>
      have hilast : i ≠ lastGroup k hk := by intro h; subst i; simp at hs
      have hslast : lastGroup k hk ∉ s := fun h => hs (Finset.mem_insert_of_mem h)
      obtain ⟨D,p,hp,hbD,hD,hsolved⟩ := ih hslast
      obtain ⟨C,q,hq,hbC,hC,hCi,hfix⟩ := exists_finish_one_square hsolver hk D hD (hbD.trans hb)
        i hilast u v huv hu hv hu0 hv0
      refine ⟨C,p.append q,?_,hbC.trans hbD,hC,?_⟩
      · rw [Path.length_append,Finset.card_insert_of_notMem his]
        calc
          p.length+q.length ≤ s.card*(cost (side n k)+9352*n)+(cost (side n k)+9352*n) :=
            Nat.add_le_add hp hq
          _ = (s.card+1)*(cost (side n k)+9352*n) := by ring
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

theorem exists_finish_path {cost : ℕ → ℕ} (hsolver : SolverCostBound cost)
    (hk : Dims n k) (B : Board n) (hB : Arranged hk B) :
    ∃ p : Path B (target n), p.length ≤ k^2*cost (side n k)+9354*k^2*n := by
  let : NeZero (side n k) := ⟨hk.side_pos.ne'⟩
  have hm : 8 ≤ side n k := by have := hk.cube_le; have := Nat.pow_le_pow_left hk.two_le 3; omega
  obtain ⟨A,p,hp,hbA,hA⟩ := exists_finish_blank_access hk B hB.sorted hB.blank_last
  obtain ⟨u,v,huv,hu,hv,hu0,hv0⟩ := exists_finish_buffers hk
  obtain ⟨D,q,hq,hbD,hD,hsolved⟩ := exists_finish_square_schedule hsolver hk A hA hbA
    u v huv hu hv hu0 hv0
  have hk2 := hk.two_le
  let d := (k-1)*side n k
  have hd : d+side n k=n := by
    dsimp [d]
    have h := Nat.sub_add_cancel (by omega : 1 ≤ k)
    calc
      (k-1)*side n k+side n k = (k-1+1)*side n k := by ring
      _ = n := by rw [h]; exact hk.mul_side
  have hprefix : ∀ x y : Fin n, x.val<d ∨ y.val<d → D (x,y)=target n (x,y) := by
    intro x y hxy
    obtain ⟨i,hi⟩ := square_covers hk (x,y)
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
  have htotal : q.length+r.length ≤ k^2*cost (side n k)+9352*(k*k-1)*n := by
    calc
      q.length+r.length ≤ (k*k-1)*(cost (side n k)+9352*n)+cost (side n k) :=
        Nat.add_le_add hq hr
      _ = (k*k-1+1)*cost (side n k)+9352*(k*k-1)*n := by ring
      _ = k^2*cost (side n k)+9352*(k*k-1)*n := by rw [hcount]; ring
  have hsub := Nat.mul_le_mul_right n (Nat.sub_le (k*k) 1)
  have hkn : n ≤ k^2*n := Nat.le_mul_of_pos_left n (by positivity)
  have hp' : p.length ≤ 2*n := hp
  nlinarith

end
end Partition
end
end SlidingPuzzle
