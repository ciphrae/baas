import SlidingPuzzle.Algorithm.Parberry.West

/-! All left-of-target cases, with a budget complementary to the right-side
budget. Their maximum yields the symmetric per-column estimate. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin n))

theorem exists_leftPlacementWord (a b i d : ℕ)
    (ha : a+i < n) (hi : 1 ≤ i) (hd : d ≤ b)
    (ha2 : a+2 < n) (hb2 : b+2 < n) (hne : i≠1 ∨ d≠0) :
    ∃ σ : List Dir, σ.length+2*(n-(b+1))+7 ≤ 8*n ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=c(a+i,b-d) ∧
      ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases htall : d+3 ≤ i
  · let v := i-d-3
    have hx : a+v+d+3=a+i := by dsimp [v]; omega
    refine ⟨westTallWord n a b d v,westTallWord_budget a b d v n (by omega) hb2 hd,?_⟩
    simpa only [hx] using westTallWord_spec a b d v (by omega : a+v+d+3 < n) hb2 hd
  by_cases hnear : i=d+2
  · have hx : a+d+2=a+i := by omega
    refine ⟨westNearWord a b d,westNearWord_budget a b d n hb2 hd,?_⟩
    simpa only [hx] using westNearWord_spec a b d (by omega : a+d+2 < n) hb2 hd
  · let e := i-1
    let v := d+1-i
    have he : v+e=d := by dsimp [v,e]; omega
    have hpos : 1 ≤ v+e := by omega
    have hx : a+e+1=a+i := by dsimp [e]; omega
    have hy : b-v-e=b-d := by omega
    refine ⟨westWideWord n a b e v,westWideWord_budget a b e v n hb2 (by omega) hpos,?_⟩
    simpa only [hx,hy] using westWideWord_spec a b e v (by omega : a+e+1 < n)
      ha2 hb2 (by omega) hpos

/-- Complete ordinary placement: the source may be anywhere outside the solved
prefix, except at the blank itself. No positional case is left as a hypothesis. -/
theorem exists_placementWord (a b : ℕ) (x y : Fin n)
    (hfree : a<x.val ∨ (a=x.val ∧ b+1≤y.val))
    (ha2 : a+2 < n) (hb2 : b+2 < n) (hne : (x,y)≠c(a+1,b)) :
    ∃ σ : List Dir, σ.length+2*min (b+1) (n-(b+1))+7 ≤ 8*n ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=(x,y) ∧
      ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases hy : b+1≤y.val
  · obtain ⟨σ,hlen,hs⟩ := exists_rightPlacementWord a b (x.val-a) (y.val-b-1)
      (by omega : a+(x.val-a) < n) (by omega : b+(y.val-b-1)+1 < n) ha2 hb2
    have he : (c(a+(x.val-a),b+(y.val-b-1)+1) : Zhong.Cell n n)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    refine ⟨σ,?_,?_⟩
    · have := min_le_left (b+1) (n-(b+1)); omega
    · simpa only [he] using hs
  · have hni : x.val-a≠1 ∨ b-y.val≠0 := by
      by_contra hh
      apply hne
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    obtain ⟨σ,hlen,hs⟩ := exists_leftPlacementWord a b (x.val-a) (b-y.val)
      (by omega : a+(x.val-a) < n) (by omega) (by omega) ha2 hb2 hni
    have he : (c(a+(x.val-a),b-(b-y.val)) : Zhong.Cell n n)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    refine ⟨σ,?_,?_⟩
    · have := min_le_right (b+1) (n-(b+1)); omega
    · simpa only [he] using hs

/-- A legal ordinary placement with the symmetric Parberry column budget. -/
theorem exists_placement [NeZero n] (B : Board n) (a b : ℕ) (x y : Fin n)
    (hfree : a<x.val ∨ (a=x.val ∧ b+1≤y.val))
    (hne : (x,y)≠blank B) (ha2 : a+2 < n) (hb2 : b+2 < n)
    (hblank : blank B=c(a+1,b)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length+2*min (b+1) (n-(b+1))+7 ≤ 8*n ∧ blank C=c(a+1,b+1) ∧
      C c(a,b+1)=B (x,y) ∧
      ∀ z, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) → C z=B z := by
  obtain ⟨σ,hlen,_,ht,hp,hfix⟩ := exists_placementWord a b x y hfree ha2 hb2
    (by simpa only [← hblank] using hne)
  obtain ⟨p,hle⟩ := path_of_zhong_word B σ
  refine ⟨Zhong.actSeq B σ,p,by omega,?_,?_,?_⟩
  · change Zhong.blank (Zhong.actSeq B σ)=_
    rw [Zhong.blank_actSeq]
    change trace (blank B) σ=_
    rw [hblank,ht]
  · rw [Zhong.actSeq_eq_permOf]
    change B (permOf (blank B) σ _)=_
    rw [hblank,hp]
  · intro z hz
    rw [Zhong.actSeq_eq_permOf]
    change B (permOf (blank B) σ z)=B z
    rw [hblank,hfix z hz]

end SlidingPuzzle.Parberry
