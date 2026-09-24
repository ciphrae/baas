import SlidingPuzzle.Algorithm.Parberry.Solver
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Algorithm.Dimension

/-! The constructed layer gives unconditional protected-prefix paths, including
arbitrary target labels. The explicit polynomial is retained before bounding it
by a uniform coefficient for the existing phase interfaces. -/
namespace SlidingPuzzle.Parberry
variable {n : ℕ} [NeZero n]

/-- Iterate the protected layer routine on shrinking residual squares. -/
theorem exists_prefix (B : Board n)
    (d : ℕ) (hd : d+4 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (15*n^2+3002*n+1)*d ∧
      ∀ x y : Fin n, x.val<d ∨ y.val<d → C (x,y)=target n (x,y) := by
  induction d with
  | zero => exact ⟨B,Path.nil B,by simp,by intros; omega⟩
  | succ d ih =>
    obtain ⟨C,p,hp,hC⟩ := ih (by omega)
    let m := n-d
    have hm : 5 ≤ m := by dsimp [m]; omega
    have hmn : m ≤ n := by dsimp [m]; omega
    have heq : d+m=n := by dsimp [m]; omega
    let : NeZero m := ⟨by omega⟩
    obtain ⟨A,hA⟩ := exists_residual_board d heq C hC
    obtain ⟨D,q,hq,hD⟩ := exists_layer hm A
    obtain ⟨E,s,hs,hE,hfix⟩ := q.exists_embedded (cornerEmbedding d heq)
      (fun x y h => by rw [cornerEmbedding_distance]; exact h)
      (cornerLabels d heq) (cornerLabels_zero d heq) C hA
    refine ⟨E,p.append s,?_,?_⟩
    · rw [Path.length_append,hs]
      have hpow := Nat.pow_le_pow_left hmn 2
      nlinarith
    · intro x y hxy
      by_cases hold : x.val<d ∨ y.val<d
      · rw [hfix (x,y) (by
          rintro ⟨z,hz⟩
          have hx := congrArg (fun w : Cell n => w.1.val) hz
          have hy := congrArg (fun w : Cell n => w.2.val) hz
          change d+z.1.val=x.val at hx
          change d+z.2.val=y.val at hy
          omega)]
        exact hC x y hold
      · have hx := x.isLt
        have hy := y.isLt
        let z : Cell m := (⟨x.val-d,by omega⟩,⟨y.val-d,by omega⟩)
        have he : cornerEmbedding d heq z=(x,y) := by
          apply Prod.ext <;> apply Fin.ext
          · change d+(x.val-d)=x.val
            omega
          · change d+(y.val-d)=y.val
            omega
        have hz : z.1.val<1 ∨ z.2.val<1 := by dsimp [z]; omega
        rw [← he,hE,hD z.1 z.2 hz,cornerLabels_target]

end SlidingPuzzle.Parberry
