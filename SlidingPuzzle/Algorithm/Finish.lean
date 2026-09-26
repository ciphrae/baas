import SlidingPuzzle.Moves.Exchange
import SlidingPuzzle.Parberry.Solver
import SlidingPuzzle.Moves.LocalSolve
import SlidingPuzzle.Algorithm.Finish.Access
import SlidingPuzzle.Moves.BorrowedSolve
import SlidingPuzzle.Moves.BlockCorner
import SlidingPuzzle.Moves.Efficiency
import SlidingPuzzle.Algorithm.ResidualPotential

/-! Phase IV (Finish). Each square of side `side n k` is solved by a local solver, with
parity repaired by borrowing a tile, and the last square is solved in place.
The local solver is abstract (`SolverBound`), with a length bound and an
inefficiency bound; both are carried through. The constructed Parberry-style
solver supplies `5*n³+O(n²)` for both. -/
namespace SlidingPuzzle
noncomputable section
open Classical

/-- A local solver with a length bound `cost` and an inefficiency bound `ineff`. -/
def SolverBound (cost ineff : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} [NeZero n], 8 ≤ n → ∀ B : ReachableBoard n,
    ∃ p : Path B.val (target n), p.length ≤ cost n ∧ p.inefficientMoves ≤ ineff n

theorem parberrySolverCost : SolverBound (fun n => 5*n^3+1509*n^2+1505*n+4796)
    (fun n => 5*n^3+1509*n^2+1505*n+4796) := by
  intro n _ hn B
  obtain ⟨p,hp⟩ := Parberry.exists_solution_cubic B (by omega)
  exact ⟨p,hp,p.inefficientMoves_le_length.trans hp⟩

section
variable {n m : ℕ} [NeZero n] [NeZero m]
theorem exists_solution_cubic_up_to_swap {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (B : Board n) (hn : 8 ≤ n)
    (a b : Cell n) (hab : a ≠ b)
    (ha : target n a ≠ 0) (hb : target n b ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost n ∧ p.inefficientMoves ≤ ineff n+2*gridDistance a b ∧
      (C = target n ∨ C = swapCells (target n) a b) := by
  classical
  by_cases hreach : Reachable B
  · obtain ⟨p,hp,hpi⟩ := hsolver hn ⟨B,hreach⟩
    exact ⟨target n,p,hp,by omega,Or.inl rfl⟩
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
  obtain ⟨p,hp,hpi⟩ := hsolver hn ⟨relabel B e,hgood⟩
  have hinv : relabel (relabel B e) e = B := by ext x; simp [relabel, e]
  have hta : (target n a).val ≠ 0 := fun h => ha (Fin.ext h)
  have htb : (target n b).val ≠ 0 := fun h => hb (Fin.ext h)
  have hq : ∃ q : Path B (relabel (target n) e), q.length ≤ cost n ∧
      q.inefficientMoves ≤ ineff n+2*gridDistance a b := by
    have hi := Path.inefficientMoves_relabel_swap_le p (target n a) (target n b) hta htb he
    have hpos : position (target n) (target n a) = a ∧ position (target n) (target n b) = b := by
      simp [position]
    rw [hpos.1, hpos.2] at hi
    have h : ∃ q : Path (relabel (relabel B e) e) (relabel (target n) e),
        q.length ≤ cost n ∧ q.inefficientMoves ≤ ineff n+2*gridDistance a b :=
      ⟨p.relabel e he,by simpa using hp,hi.trans (by omega)⟩
    rwa [hinv] at h
  obtain ⟨q,hq,hqi⟩ := hq
  refine ⟨_,q,hq,hqi,Or.inr ?_⟩
  simp [e,relabel_swap]

theorem exists_borrowed_solution {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (B T : Board n) (hm : 8 ≤ m)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hT : ∀ c, position (target n) (T (blockEmbedding ro co hr hc c)) =
      blockEmbedding ro co hr hc c)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (hcorner : B (blockEmbedding ro co hr hc (blank (target m))) =
      T (blockEmbedding ro co hr hc (blank (target m))))
    (a b : Cell m) (hab : a ≠ b) (ha : a ≠ blank (target m)) (hb' : b ≠ blank (target m)) :
    ∃ F : Board n, ∃ r : Path B F,
      r.length ≤ cost m+4*n ∧ r.inefficientMoves ≤ ineff m+2*gridDistance a b+4*n ∧
      blank F = blank B ∧
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
  obtain ⟨D,q,hq,hqi,hD⟩ := exists_solution_cubic_up_to_swap hsolver A hm a b hab hta htb
  have hDz : blank D = z := by
    rcases hD with rfl | rfl
    · rfl
    · change Equiv.swap a b z = z
      exact Equiv.swap_apply_of_ne_of_ne ha.symm hb'.symm
  obtain ⟨E,s,hs,hsi,hE,hfix⟩ := q.exists_embedded_efficient ι
    (fun x y => blockEmbedding_distance _ _ _ _ x y) η (borrowedLabels_zero _ _ _) (by
      intro l hl
      have hd : position (target m) l ≠ z := by
        intro h
        apply hl
        have := congrArg (target m) h
        simpa [position, z, blank] using this
      have hη : η l = T (ι (position (target m) l)) := by
        rw [show l = target m (position (target m) l) by simp [position]]
        rw [borrowedLabels_target ι T hzero _ hd]
        simp [position]
      rw [hη, hT]) C hA
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
  obtain ⟨F,r,hlen,hri,hbF,hF,hFfix⟩ := p.exists_conjugated_efficient s hbE S haccess hlocal
  have hFcorner : F (ι z) = T (ι z) := by
    rw [hFfix]
    · exact hcorner
    · rintro ⟨c,hc,he⟩
      exact hc (ι.injective he)
  have hFn (c : Cell m) (hc : c ≠ z) : F (ι c) = η (D c) := by
    rw [hF _ ⟨c,hc,rfl⟩,hE]
  refine ⟨F,r,by omega,by omega,hbF,?_,?_⟩
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

theorem exists_block_finish {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (B T : Board n) (hm : 8 ≤ m) (hn : 4 ≤ n)
    (ro co : ℕ) (hr : ro+m ≤ n) (hc : co+m ≤ n)
    (hb : blank B = blank (target n))
    (hzero : ∀ c, T (blockEmbedding ro co hr hc c) ≠ 0)
    (hT : ∀ c, position (target n) (T (blockEmbedding ro co hr hc c)) =
      blockEmbedding ro co hr hc c)
    (hlabels : ∀ c, ∃ d, B (blockEmbedding ro co hr hc c) = T (blockEmbedding ro co hr hc d))
    (u v : Cell n) (huv : u ≠ v)
    (hu : u ∉ Set.range (blockEmbedding ro co hr hc))
    (hv : v ∉ Set.range (blockEmbedding ro co hr hc))
    (hu0 : B u ≠ 0) (hv0 : B v ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost m+9352*n ∧ p.inefficientMoves ≤ ineff m+9353*n ∧ blank C = blank B ∧
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
  obtain ⟨E,q,hq,hqi,hbE,hE,hEfix⟩ := exists_borrowed_solution hsolver D T hm ro co hr hc
    (hbD.trans hb) hzero hT hDlabels hDz a b hab haz hbz
  have hab1 : gridDistance a b = 1 := by simp [a, b, gridDistance, Nat.dist]
  have hout (x : Cell n) (hx : x ∉ Set.range ι) : E x = B x :=
    (hEfix x hx).trans (hDfix x hx)
  have hEu : E u=B u := hout u hu
  have hEv : E v=B v := hout v hv
  rcases hE with hE | hE
  · refine ⟨E,p.append q,?_,?_,hbE.trans hbD,hE,Or.inl ⟨hEu,hEv⟩,?_⟩
    · rw [Path.length_append]; omega
    · rw [Path.inefficientMoves_append]
      have := p.inefficientMoves_le_length
      omega
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
    refine ⟨C,(p.append q).append s,?_,?_,hbC.trans (hbE.trans hbD),?_,
      Or.inr ⟨hCu.trans hEv,hCv.trans hEu⟩,?_⟩
    · simp only [Path.length_append]; omega
    · simp only [Path.inefficientMoves_append]
      have := p.inefficientMoves_le_length
      have := s.inefficientMoves_le_length
      omega
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
theorem exists_finish_one_square {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (hk : FDims n k) (B : Board n)
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target n))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk)
    (u v : Cell n) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target n)) (hv0 : v ≠ blank (target n)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ cost (side n k)+9352*n ∧ p.inefficientMoves ≤ ineff (side n k)+9353*n ∧
      blank C = blank B ∧ SquaresSorted (k := k) C ∧
      (∀ x, square i x → C x = target n x) ∧
      (∀ (j : GroupIndex k), j ≠ i → j ≠ lastGroup k hk →
        ∀ x, square j x → C x = B x) := by
  classical
  let : NeZero (side n k) := ⟨hk.side_pos.ne'⟩
  have hm : 8 ≤ side n k := hk.eight_le
  have hn : 4 ≤ n := hk.two_le_n
  have hBu : B u ≠ 0 := by
    intro h
    exact hu0 ((B.injective (h.trans (B.apply_symm_apply 0).symm)).trans hb)
  have hBv : B v ≠ 0 := by
    intro h
    exact hv0 ((B.injective (h.trans (B.apply_symm_apply 0).symm)).trans hb)
  have huout : u ∉ Set.range (squareEmbedding i) := by
    intro h
    exact hi (hk.square_unique ((mem_range_squareEmbedding hk i u).mp h) hu)
  have hvout : v ∉ Set.range (squareEmbedding i) := by
    intro h
    exact hi (hk.square_unique ((mem_range_squareEmbedding hk i v).mp h) hv)
  obtain ⟨C,p,hp,hpi,hbC,hC,hbuf,hfix⟩ := exists_block_finish hsolver B (target n) hm hn
    ((groupRow i).val*side n k) ((groupCol i).val*side n k)
    (by simpa [Nat.add_mul] using square_block_end (n := n) (groupRow i))
    (by simpa [Nat.add_mul] using square_block_end (n := n) (groupCol i)) hb
    (squareEmbedding_target_nonzero hk i hi) (fun c => by simp [position])
    (squaresSorted_block_labels hk B hB hb i hi)
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
  refine ⟨C,p,?_,?_,hbC,?_,hsolved,?_⟩
  · simpa [← pow_mul] using hp
  · simpa [← pow_mul] using hpi
  · intro j x hx hnonzero
    by_cases hxi : square i x
    · rw [hsolved x hxi] at hnonzero ⊢
      exact (mem_targetGroup j _).mpr ⟨hnonzero,by simpa [position] using hx⟩
    by_cases hxu : x=u
    · subst x
      have he : j=lastGroup k hk := hk.square_unique hx hu
      rwa [he]
    by_cases hxv : x=v
    · subst x
      have he : j=lastGroup k hk := hk.square_unique hx hv
      rwa [he]
    have hnot : x ∉ Set.range (squareEmbedding i) :=
      fun h => hxi ((mem_range_squareEmbedding hk i x).mp h)
    rw [hfix x hnot hxu hxv] at hnonzero ⊢
    exact hB j x hx hnonzero
  · intro j hji hjlast x hx
    apply hfix
    · intro h
      exact hji (hk.square_unique hx ((mem_range_squareEmbedding hk i x).mp h))
    · intro he
      subst x
      exact hjlast (hk.square_unique hx hu)
    · intro he
      subst x
      exact hjlast (hk.square_unique hx hv)

theorem exists_finish_square_schedule {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (hk : FDims n k) (B : Board n)
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target n))
    (u v : Cell n) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target n)) (hv0 : v ≠ blank (target n)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (k*k-1)*(cost (side n k)+9352*n) ∧
      p.inefficientMoves ≤ (k*k-1)*(ineff (side n k)+9353*n) ∧
      blank C = blank B ∧ SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k), i ≠ lastGroup k hk → ∀ x, square i x → C x = target n x := by
  classical
  have schedule (s : Finset (GroupIndex k)) (hs : lastGroup k hk ∉ s) :
      ∃ C : Board n, ∃ p : Path B C,
        p.length ≤ s.card*(cost (side n k)+9352*n) ∧
        p.inefficientMoves ≤ s.card*(ineff (side n k)+9353*n) ∧
        blank C = blank B ∧ SquaresSorted (k := k) C ∧
        ∀ i ∈ s, ∀ x, square i x → C x=target n x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨B,Path.nil B,by simp,by simp [Path.inefficientMoves],rfl,hB,by simp⟩
    | @insert i s his ih =>
      have hilast : i ≠ lastGroup k hk := by intro h; subst i; simp at hs
      have hslast : lastGroup k hk ∉ s := fun h => hs (Finset.mem_insert_of_mem h)
      obtain ⟨D,p,hp,hpi,hbD,hD,hsolved⟩ := ih hslast
      obtain ⟨C,q,hq,hqi,hbC,hC,hCi,hfix⟩ := exists_finish_one_square hsolver hk D hD
        (hbD.trans hb) i hilast u v huv hu hv hu0 hv0
      refine ⟨C,p.append q,?_,?_,hbC.trans hbD,hC,?_⟩
      · rw [Path.length_append,Finset.card_insert_of_notMem his]
        calc
          p.length+q.length ≤ s.card*(cost (side n k)+9352*n)+(cost (side n k)+9352*n) :=
            Nat.add_le_add hp hq
          _ = (s.card+1)*(cost (side n k)+9352*n) := by ring
      · rw [Path.inefficientMoves_append,Finset.card_insert_of_notMem his]
        calc
          p.inefficientMoves+q.inefficientMoves ≤
              s.card*(ineff (side n k)+9353*n)+(ineff (side n k)+9353*n) :=
            Nat.add_le_add hpi hqi
          _ = (s.card+1)*(ineff (side n k)+9353*n) := by ring
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hCi x hx
        · have hji : j ≠ i := fun h => his (h ▸ hj)
          have hjlast : j ≠ lastGroup k hk := fun h => hslast (h ▸ hj)
          rw [hfix j hji hjlast x hx]
          exact hsolved j hj x hx
  obtain ⟨C,p,hp,hpi,hbC,hC,hsolved⟩ := schedule (Finset.univ.erase (lastGroup k hk)) (by simp)
  refine ⟨C,p,?_,?_,hbC,hC,?_⟩
  · simpa using hp
  · simpa using hpi
  · intro i hi x hx
    exact hsolved i (by simp [hi]) x hx

/-- Finish under the weak dimensions `FDims`: every tile lies in its own square
and the blank lies in the last square. -/
theorem exists_finish_path_of {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (hk : FDims n k) (B : Board n) (hBr : Reachable B) (hBs : SquaresSorted (k := k) B)
    (hBb : square (lastGroup k hk) (blank B)) :
    ∃ p : Path B (target n), p.length ≤ k^2*cost (side n k)+9354*k^2*n ∧
      p.inefficientMoves ≤ k^2*ineff (side n k)+9354*k^2*n := by
  let : NeZero (side n k) := ⟨hk.side_pos.ne'⟩
  have hm : 8 ≤ side n k := hk.eight_le
  obtain ⟨A,p,hp,hbA,hA⟩ := exists_finish_blank_access hk B hBs hBb
  obtain ⟨u,v,huv,hu,hv,hu0,hv0⟩ := exists_finish_buffers hk
  obtain ⟨D,q,hq,hqi,hbD,hD,hsolved⟩ := exists_finish_square_schedule hsolver hk A hA hbA
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
    obtain ⟨i,hi⟩ := hk.square_covers (x,y)
    apply hsolved i _ (x,y) hi
    intro he
    rw [he] at hi
    simp only [square,lastGroup,groupRow,groupCol,Equiv.symm_apply_apply] at hi
    dsimp [d] at hxy
    omega
  have hreach : Reachable D := by
    obtain ⟨r⟩ := hBr
    exact ⟨(r.append p).append q⟩
  obtain ⟨R,hR⟩ := exists_residual_board d hd D hprefix
  have hrR : Reachable R := residual_reachable (by omega) d hd D hprefix R hR hreach
  obtain ⟨r,hr,hri⟩ := hsolver hm ⟨R,hrR⟩
  obtain ⟨s,hs⟩ := residual_solution_lifts d hd D hprefix R hR r
  have hsi : s.inefficientMoves = r.inefficientMoves := by
    have h₁ := s.solution_length
    have h₂ := r.solution_length
    rw [residual_manhattan_eq d hd D hprefix R hR] at h₁
    change r.length = manhattan R + 2 * r.inefficientMoves at h₂
    omega
  have hcount : k*k-1+1 = k*k := Nat.sub_add_cancel (by nlinarith)
  have hsub := Nat.mul_le_mul_right n (Nat.sub_le (k*k) 1)
  have hkn : n ≤ k^2*n := Nat.le_mul_of_pos_left n (by positivity)
  have hp' : p.length ≤ 2*n := hp
  refine ⟨(p.append q).append s,?_,?_⟩
  swap
  · simp only [Path.inefficientMoves_append,hsi]
    have hpi := p.inefficientMoves_le_length
    have htotal : q.inefficientMoves+r.inefficientMoves ≤
        k^2*ineff (side n k)+9353*(k*k-1)*n := by
      calc
        q.inefficientMoves+r.inefficientMoves ≤
            (k*k-1)*(ineff (side n k)+9353*n)+ineff (side n k) := Nat.add_le_add hqi hri
        _ = (k*k-1+1)*ineff (side n k)+9353*(k*k-1)*n := by ring
        _ = k^2*ineff (side n k)+9353*(k*k-1)*n := by rw [hcount]; ring
    nlinarith
  simp only [Path.length_append,hs]
  have htotal : q.length+r.length ≤ k^2*cost (side n k)+9352*(k*k-1)*n := by
    calc
      q.length+r.length ≤ (k*k-1)*(cost (side n k)+9352*n)+cost (side n k) :=
        Nat.add_le_add hq hr
      _ = (k*k-1+1)*cost (side n k)+9352*(k*k-1)*n := by ring
      _ = k^2*cost (side n k)+9352*(k*k-1)*n := by rw [hcount]; ring
  nlinarith


theorem exists_finish_path {cost ineff : ℕ → ℕ} (hsolver : SolverBound cost ineff)
    (hk : Dims n k) (B : Board n) (hB : Arranged hk B) :
    ∃ p : Path B (target n), p.length ≤ k^2*cost (side n k)+9354*k^2*n ∧
      p.inefficientMoves ≤ k^2*ineff (side n k)+9354*k^2*n :=
  exists_finish_path_of hsolver hk.toFDims B hB.reachable hB.sorted hB.blank_last

end
end Partition
end
end SlidingPuzzle
