import SlidingPuzzle.Algorithm.Parberry.Reduction
import SlidingPuzzle.Moves.Prefix

/-! A Parberry layer routine also gives the shared fifteen-quadratic protected
prefix. No reachability hypothesis is imposed on the staging target board. -/
namespace SlidingPuzzle.Parberry
variable {n : ℕ} [NeZero n]

/-- Iterate the protected layer routine on shrinking residual squares. -/
theorem exists_prefix_of_layer (hlayer : LayerPathBound) (B : Board n)
    (d : ℕ) (hd : d+4 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 15*d*n^2 ∧
      ∀ x y : Fin n, x.val<d ∨ y.val<d → C (x,y)=target n (x,y) := by
  induction d with
  | zero => exact ⟨B,Path.nil B,by simp,by intros; omega⟩
  | succ d ih =>
    obtain ⟨C,p,hp,hC⟩ := ih (by omega)
    let m := n-d
    have hm : 3 ≤ m := by dsimp [m]; omega
    have hmn : m ≤ n := by dsimp [m]; omega
    have heq : d+m=n := by dsimp [m]; omega
    let : NeZero m := ⟨by omega⟩
    obtain ⟨A,hA⟩ := exists_residual_board d heq C hC
    obtain ⟨D,q,hq,hD⟩ := hlayer m hm A
    obtain ⟨E,s,hs,hE,hfix⟩ := q.exists_embedded (cornerEmbedding d heq)
      (fun x y h => by rw [cornerEmbedding_distance]; exact h)
      (cornerLabels d heq) (cornerLabels_zero d heq) C hA
    refine ⟨E,p.append s,?_,?_⟩
    · rw [Path.length_append,hs]
      have hq' : q.length ≤ 15*m^2 := by omega
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

/-- The layer routine supplies exactly the prefix interface used by both
Preparation and the arbitrary-dimension reduction, including arbitrary labels. -/
theorem prefixPathBound_of_layer (h : LayerPathBound) : PrefixPathBound 15 := by
  intro n _ B T hblank d hd
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e 0=0 := by
    change target n (blank T)=0
    rw [hblank]
    simp [blank,position]
  have hes : e.symm 0=0 := by
    apply e.injective
    simpa [he] using e.apply_symm_apply 0
  obtain ⟨D,p,hp,hD⟩ := exists_prefix_of_layer h (relabel B e) d hd
  have hq : ∃ q : Path B (relabel D e.symm), q.length ≤ 15*d*n^2 := by
    have hh : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
        q.length ≤ 15*d*n^2 := ⟨p.relabel e.symm hes,by simpa using hp⟩
    rwa [relabel_relabel_symm] at hh
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm,q,hq,?_⟩
  intro x y hxy
  change e.symm (D (x,y))=T (x,y)
  rw [hD x y hxy]
  simp [e]
end SlidingPuzzle.Parberry
