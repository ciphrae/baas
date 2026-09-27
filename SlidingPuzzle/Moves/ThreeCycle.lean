import SlidingPuzzle.Algorithm.Allocation
import SlidingPuzzle.Moves.Conjugation
import SlidingPuzzle.Moves.TopPrefix
import SlidingPuzzle.Moves.TopCycle

/-! Three-tile rotations anywhere on the board, with linear move cost. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Stage any three distinct nonblank tiles in the top row, with the blank below.
Only this temporary staging step is allowed to disturb other tiles. -/
theorem exists_stage_three (B : Board n) (hn : 4 ≤ n)
    (a b c : Cell n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : B a ≠ 0) (hb : B b ≠ 0) (hc : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length + 8 ≤ 126*n ∧ blank C = (⟨1,by omega⟩,0) ∧
      C (0,0) = B a ∧ C (0,⟨1,by omega⟩) = B b ∧
      C (0,⟨2,by omega⟩) = B c := by
  classical
  let u : Fin 3 ↪ Cell n := ⟨fun i => (0,⟨i.val,by omega⟩), by
    intro i j h
    exact Fin.ext (congrArg (fun x : Cell n => x.2.val) h)⟩
  let v : Fin 3 → Cell n := ![a,b,c]
  have hv : Function.Injective v := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [v]
  let f : Fin 3 ↪ Tile n := ⟨fun i => B (v i), B.injective.comp hv⟩
  have hf : ∀ i, f i ≠ 0 := by
    intro i
    fin_cases i <;> simpa [f,v] using (by assumption : B _ ≠ 0)
  have hu : ∀ i, target n (u i) ≠ 0 := by
    intro i
    exact Zhong.target_ne_zero 0 i.val (by omega) (by omega)
  obtain ⟨T,hT,hTu⟩ := exists_board_extending_cell_embedding u f hu hf
  obtain ⟨D,p,hp,hD⟩ := exists_top_three_prefix_path_relabel B T hn hT
  have hplaced (i : Fin 3) : D (u i) = B (v i) :=
    (hD ⟨i.val,by omega⟩ i.isLt).trans (hTu i)
  have hnonzero (j : Fin n) (hj : j.val < 3) : D (0,j) ≠ 0 := by
    have h := hplaced ⟨j.val,hj⟩
    change D (0,j) = B (v ⟨j.val,hj⟩) at h
    rw [h]
    exact hf ⟨j.val,hj⟩
  obtain ⟨C,q,hq,hbC,hfix⟩ := exists_blank_below_top_prefix D (by omega) 3 hnonzero
  refine ⟨C,p.append q,?_,hbC,?_,?_,?_⟩
  · rw [Path.length_append]
    omega
  · exact (hfix 0 (by simp)).trans (hplaced 0)
  · exact (hfix ⟨1,by omega⟩ (by simp)).trans (hplaced 1)
  · exact (hfix ⟨2,by omega⟩ (by simp)).trans (hplaced 2)

/-- Rotate any three distinct nonblank tiles, restore every other tile, and return
the blank to its original cell. The bound counts all staging and unstaging moves. -/
theorem exists_three_cycle (B : Board n) (hn : 4 ≤ n)
    (a b c : Cell n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : B a ≠ 0) (hb : B b ≠ 0) (hc : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 254*n ∧ blank C = blank B ∧
      C a = B b ∧ C b = B c ∧ C c = B a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
  obtain ⟨D,p,hp,hbD,hDa,hDb,hDc⟩ := exists_stage_three B hn a b c hab hac hbc ha hb hc
  obtain ⟨E,q,hq,hbE,hEa,hEb,hEc,hfix⟩ := exists_top_three_cycle D hn hbD
  obtain ⟨F,r,hr,hbF,hF⟩ := p.exists_unstaged q hbE
  have hposa : D.symm (B a) = (0,0) := by rw [← hDa]; simp
  have hposb : D.symm (B b) = (0,⟨1,by omega⟩) := by rw [← hDb]; simp
  have hposc : D.symm (B c) = (0,⟨2,by omega⟩) := by rw [← hDc]; simp
  refine ⟨F,r,by omega,hbF,?_,?_,?_,?_⟩
  · rw [hF,hposa,hEa,hDb]
  · rw [hF,hposb,hEb,hDc]
  · rw [hF,hposc,hEc,hDa]
  · intro x hxa hxb hxc
    rw [hF,hfix]
    · exact D.apply_symm_apply (B x)
    · intro h
      apply hxa
      exact B.injective (by rw [← D.apply_symm_apply (B x),h,hDa])
    · intro h
      apply hxb
      exact B.injective (by rw [← D.apply_symm_apply (B x),h,hDb])
    · intro h
      apply hxc
      exact B.injective (by rw [← D.apply_symm_apply (B x),h,hDc])
end SlidingPuzzle
