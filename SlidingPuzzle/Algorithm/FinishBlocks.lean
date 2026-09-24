import SlidingPuzzle.Moves.BlockFinish
import SlidingPuzzle.Algorithm.SquareGeometry

/-! Solve nonfinal squares directly, using two tiles of the final square as buffers. -/
namespace SlidingPuzzle.Partition
variable {k : ℕ} [NeZero (k^4)]

/-- Finish one nonfinal square in cubic local cost. Other nonfinal squares stay
fixed, and all square memberships and the global corner blank are retained. -/
theorem exists_finish_one_square_of_solver {K : ℕ} (hsolver : CubicSolverBound K)
    (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk)
    (u v : Cell (k^4)) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target (k^4))) (hv0 : v ≠ blank (target (k^4))) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ K*k^9+9352*k^4 ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
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
  obtain ⟨C,p,hp,hbC,hC,hbuf,hfix⟩ := exists_block_finish_of_solver hsolver B (target (k^4)) hm hn
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

/-- Specialize the solver-parametric construction to the checked cubic solver. -/
theorem exists_finish_one_square (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (i : GroupIndex k) (hi : i ≠ lastGroup k hk)
    (u v : Cell (k^4)) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target (k^4))) (hv0 : v ≠ blank (target (k^4))) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ 527*k^9+9352*k^4 ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      (∀ x, square i x → C x = target (k^4) x) ∧
      (∀ (j : GroupIndex k), j ≠ i → j ≠ lastGroup k hk →
        ∀ x, square j x → C x = B x) := by
  exact exists_finish_one_square_of_solver cubicSolverBound_current hk B hB hb i hi u v huv hu hv hu0 hv0

/-- Run the direct square solver once per nonfinal square. -/
theorem exists_finish_square_schedule_of_solver {K : ℕ} (hsolver : CubicSolverBound K)
    (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (u v : Cell (k^4)) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target (k^4))) (hv0 : v ≠ blank (target (k^4))) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (k*k-1)*(K*k^9+9352*k^4) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k), i ≠ lastGroup k hk → ∀ x, square i x → C x = target (k^4) x := by
  classical
  have schedule (s : Finset (GroupIndex k)) (hs : lastGroup k hk ∉ s) :
      ∃ C : Board (k^4), ∃ p : Path B C,
        p.length ≤ s.card*(K*k^9+9352*k^4) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
        ∀ i ∈ s, ∀ x, square i x → C x=target (k^4) x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨B,Path.nil B,by simp,rfl,hB,by simp⟩
    | @insert i s his ih =>
      have hilast : i ≠ lastGroup k hk := by intro h; subst i; simp at hs
      have hslast : lastGroup k hk ∉ s := fun h => hs (Finset.mem_insert_of_mem h)
      obtain ⟨D,p,hp,hbD,hD,hsolved⟩ := ih hslast
      obtain ⟨C,q,hq,hbC,hC,hCi,hfix⟩ := exists_finish_one_square_of_solver hsolver hk D hD (hbD.trans hb)
        i hilast u v huv hu hv hu0 hv0
      refine ⟨C,p.append q,?_,hbC.trans hbD,hC,?_⟩
      · rw [Path.length_append,Finset.card_insert_of_notMem his]
        calc
          p.length+q.length ≤ s.card*(K*k^9+9352*k^4)+(K*k^9+9352*k^4) :=
            Nat.add_le_add hp hq
          _ = (s.card+1)*(K*k^9+9352*k^4) := by ring
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

/-- Specialize the solver-parametric construction to the checked cubic solver. -/
theorem exists_finish_square_schedule (hk : 2 ≤ k) (B : Board (k^4))
    (hB : SquaresSorted (k := k) B) (hb : blank B = blank (target (k^4)))
    (u v : Cell (k^4)) (huv : u ≠ v)
    (hu : square (lastGroup k hk) u) (hv : square (lastGroup k hk) v)
    (hu0 : u ≠ blank (target (k^4))) (hv0 : v ≠ blank (target (k^4))) :
    ∃ C : Board (k^4), ∃ p : Path B C,
      p.length ≤ (k*k-1)*(527*k^9+9352*k^4) ∧ blank C = blank B ∧ SquaresSorted (k := k) C ∧
      ∀ (i : GroupIndex k), i ≠ lastGroup k hk → ∀ x, square i x → C x = target (k^4) x := by
  exact exists_finish_square_schedule_of_solver cubicSolverBound_current hk B hB hb u v huv hu hv hu0 hv0

end SlidingPuzzle.Partition
