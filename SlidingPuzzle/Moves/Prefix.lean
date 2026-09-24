import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Algorithm.Dimension

/-! Quantitative legal paths that place an outer prefix against a prescribed target. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Place the first `d` rows and columns, retaining a square of side at least four.
The target may be any labeling whose blank is in the standard corner. -/
theorem exists_prefix_path (B T : Board n) (hblank : blank T = blank (target n))
    (d : ℕ) (hd : d+4 ≤ n) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 1004*d*n^2 ∧
      ∀ x y : Fin n, x.val<d ∨ y.val<d → C (x,y)=T (x,y) := by
  induction d with
  | zero =>
      exact ⟨B,Path.nil B,by simp,fun x y h => by omega⟩
  | succ d ih =>
      obtain ⟨D,p,hp,hD⟩ := ih (by omega)
      obtain ⟨E,q,hq,hqa,hqc,hqcol⟩ := exists_protected_column_path_relabel
        d (by omega) (by omega) D T hblank
        (fun x y hx => hD x y (Or.inl hx))
        (fun x y hy => hD x y (Or.inr hy))
      have hEcol (x y : Fin n) (hy : y.val<d+1) : E (x,y)=T (x,y) := by
        by_cases h : y.val<d
        · exact (hqc x y h).trans (hD x y (Or.inr h))
        · have he : y=(⟨d,by omega⟩ : Fin n) := Fin.ext (show y.val=d by omega)
          rw [he]
          exact hqcol x
      obtain ⟨F,s,hs,hsa,hsc,hsrow⟩ := exists_protected_row_path_relabel
        d (by omega) (by omega) (by omega) (d+1) (by omega) E T hblank
        (fun x y hx => (hqa x y hx).trans (hD x y (Or.inl hx))) hEcol
      refine ⟨F,(p.append q).append s,?_,?_⟩
      · have hq' : q.length ≤ 502*n^2 := by
          calc
            _ ≤ (n-d)*(251*(n+n)) := hq
            _ ≤ n*(251*(n+n)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
            _ = _ := by ring
        have hs' : s.length ≤ 502*n^2 := by
          calc
            _ ≤ (n-(d+1))*(251*(n+n)) := hs
            _ ≤ n*(251*(n+n)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
            _ = _ := by ring
        simp only [Path.length_append]
        nlinarith
      · intro x y h
        rcases h with hx | hy
        · by_cases hxd : x.val<d
          · exact (hsa x y hxd).trans ((hqa x y hxd).trans (hD x y (Or.inl hxd)))
          · have he : x=(⟨d,by omega⟩ : Fin n) := Fin.ext (show x.val=d by omega)
            rw [he]
            exact hsrow y
        · exact (hsc x y hy).trans (hEcol x y hy)

/-- The general-dimension prefix has the paper's `O(k¹¹)` length budget. -/
theorem exists_fourth_power_prefix (B : Board n) (k : ℕ) (hk : 2 ≤ k)
    (hlo : k^4 ≤ n) (hhi : n < (k+1)^4) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 3855360*k^11 ∧
      ∀ x y : Fin n, x.val<n-k^4 ∨ y.val<n-k^4 → C (x,y)=target n (x,y) := by
  have hk4 : 4 ≤ k^4 := by nlinarith [sq_nonneg (k^2-2)]
  obtain ⟨C,p,hp,hC⟩ := exists_prefix_path B (target n) rfl (n-k^4) (by omega)
  refine ⟨C,p,?_,hC⟩
  have h := outer_layer_budget_le (by omega : 1 ≤ k) hhi
  calc
    _ ≤ 1004*(n-k^4)*n^2 := hp
    _ = 1004*((n-k^4)*n^2) := by ring
    _ ≤ 1004*(3840*k^11) := Nat.mul_le_mul_left 1004 h
    _ = _ := by ring

/-- A reusable protected row/column prefix cost, for arbitrary target labels
with the standard blank corner. -/
def PrefixPathBound (P : ℕ) : Prop :=
  ∀ {m : ℕ} [NeZero m] (B T : Board m),
    blank T = blank (target m) → ∀ (d : ℕ), d+4 ≤ m →
    ∃ C : Board m, ∃ p : Path B C,
      p.length ≤ P*d*m^2 ∧
      ∀ x y : Fin m, x.val<d ∨ y.val<d → C (x,y)=T (x,y)

theorem prefixPathBound_current : PrefixPathBound 1004 := by
  intro m _ B T hblank d hd
  exact exists_prefix_path B T hblank d hd
end SlidingPuzzle
