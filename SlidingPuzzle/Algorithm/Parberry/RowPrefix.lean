import SlidingPuzzle.Algorithm.Parberry.LeftPlacement
import SlidingPuzzle.Target

/-! Actual row-prefix assembly using the complete ordinary placement routine.
Only the first column is assumed placed; the subsequent source positions are
obtained from the board and all eligibility facts are proved. -/
namespace SlidingPuzzle.Parberry
variable {n : ℕ} [NeZero n]
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin n))

/-- Per-column move allowance, including the blank routing for that step. -/
def rowStepBudget (n j : ℕ) : ℕ := 8*n-(2*min j (n-j)+7)

/-- The exact sum of the ordinary placement allowances for columns `1,…,d`. -/
def rowPrefixBudget (n d : ℕ) : ℕ := ∑ j ∈ Finset.range d, rowStepBudget n (j+1)

/-- Select the correct tile from the board and place it, proving that its source
is outside the protected prefix and is not the blank. -/
theorem exists_correct_placement (B : Board n) (a b : ℕ)
    (ha2 : a+2 < n) (hb2 : b+2 < n)
    (hblank : blank B=c(a+1,b))
    (hfixed : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
      B z=target n z) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ rowStepBudget n (b+1) ∧ blank C=c(a+1,b+1) ∧
      ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+2) →
        C z=target n z := by
  let s := B.symm (target n c(a,b+1))
  have hs : B s=target n c(a,b+1) := B.apply_symm_apply _
  have hfree : a < s.1.val ∨ (a=s.1.val ∧ b+1 ≤ s.2.val) := by
    by_contra hh
    have hfixeds := hfixed s (by omega)
    have he : s=c(a,b+1) := (target n).injective (hfixeds.symm.trans hs)
    have hx := congrArg (fun z : Cell n => z.1.val) he
    have hy := congrArg (fun z : Cell n => z.2.val) he
    simp only [Fin.val_mk] at hx hy
    omega
  have hne : s≠blank B := by
    intro he
    have hzero : target n c(a,b+1)=0 := by rw [← hs,he]; exact B.apply_symm_apply 0
    have ht := (target n).injective (hzero.trans (target_bottomRight n).symm)
    have hx := congrArg (fun z : Cell n => z.1.val) ht
    simp only [Fin.val_mk] at hx
    omega
  obtain ⟨C,p,hp,hblankC,hC,hfix⟩ := exists_placement B a b s.1 s.2 hfree hne ha2 hb2 hblank
  refine ⟨C,p,?_,hblankC,?_⟩
  · dsimp [rowStepBudget]; omega
  · intro z hz
    by_cases hprev : z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1)
    · exact (hfix z hprev).trans (hfixed z hprev)
    · have he : z=c(a,b+1) := by
        apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
      rw [he,hC,hs]

/-- Starting with the first tile placed, construct the next `d` placements.
The final blank position is normalized without an extra charge per step. -/
theorem exists_row_prefix (B : Board n) (a d : ℕ) (ha2 : a+2 < n) (hd : d+2 ≤ n)
    (hblank : blank B=c(a+1,0))
    (hfixed : ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<1) → B z=target n z) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ rowPrefixBudget n d ∧ blank C=c(a+1,d) ∧
      ∀ z : Cell n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<d+1) → C z=target n z := by
  induction d with
  | zero =>
      exact ⟨B,Path.nil B,by simp [rowPrefixBudget],hblank,hfixed⟩
  | succ d ih =>
      obtain ⟨C,p,hp,hblankC,hC⟩ := ih (by omega) hblank
      obtain ⟨D,q,hq,hblankD,hD⟩ := exists_correct_placement C a d ha2 (by omega) hblankC hC
      refine ⟨D,p.append q,?_,hblankD,?_⟩
      · rw [Path.length_append]
        simpa only [rowPrefixBudget,Finset.sum_range_succ] using Nat.add_le_add hp hq
      · simpa only [Nat.add_assoc] using hD

end SlidingPuzzle.Parberry
