import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Bridge.Reachability
import SlidingPuzzle.Moves.Embedding

/-! Cubic local solving without assuming the local parity condition. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Exchanging two labels is the same board operation as exchanging their cells. -/
theorem relabel_swap (B : Board n) (a b : Tile n) :
    relabel B (Equiv.swap a b) = swapCells B (B.symm a) (B.symm b) := by
  have h := Equiv.trans_swap_trans_symm a b B
  have hh := congrArg (fun e => e.trans B) h
  simpa [relabel,swapCells,Equiv.trans_assoc] using hh

/-- An arbitrary local board can be solved in cubic length up to a specified
nonblank transposition. This explicitly handles a locally odd permutation. -/
theorem exists_solution_cubic_up_to_swap_of_solver {K : ℕ} (hsolver : CubicSolverBound K)
    (B : Board n) (hn : 8 ≤ n)
    (a b : Cell n) (hab : a ≠ b)
    (ha : target n a ≠ 0) (hb : target n b ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ K*n^3 ∧ (C = target n ∨ C = swapCells (target n) a b) := by
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
  have hq : ∃ q : Path B (relabel (target n) e.symm), q.length ≤ K*n^3 := by
    have h : ∃ q : Path (relabel (relabel B e) e.symm) (relabel (target n) e.symm),
        q.length ≤ K*n^3 := ⟨p.relabel e.symm hes,by simpa using hp⟩
    rwa [relabel_relabel_symm] at h
  obtain ⟨q,hq⟩ := hq
  refine ⟨_,q,hq,Or.inr ?_⟩
  simp [e,relabel_swap]

/-- Specialize the solver-parametric construction to the checked cubic solver. -/
theorem exists_solution_cubic_up_to_swap (B : Board n) (hn : 8 ≤ n)
    (a b : Cell n) (hab : a ≠ b)
    (ha : target n a ≠ 0) (hb : target n b ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 527*n^3 ∧ (C = target n ∨ C = swapCells (target n) a b) := by
  exact exists_solution_cubic_up_to_swap_of_solver cubicSolverBound_current B hn a b hab ha hb

omit [NeZero n] in
/-- A finite embedded set of labels determines an actual local board. -/
theorem exists_board_of_embedded_labels {m : ℕ} (ι : Cell m ↪ Cell n)
    (η : Tile m ↪ Tile n) (B : Board n)
    (hlabels : ∀ c, B (ι c) ∈ Set.range η) :
    ∃ A : Board m, ∀ c, B (ι c) = η (A c) := by
  classical
  choose f hf using hlabels
  have hinj : Function.Injective f := by
    intro a b h
    exact ι.injective (B.injective (by rw [← hf a,← hf b,h]))
  have hcard : Fintype.card (Cell m) = Fintype.card (Tile m) := by simp
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩
  exact ⟨Equiv.ofBijective f hsurj,fun c => (hf c).symm⟩
end SlidingPuzzle
