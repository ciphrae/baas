import SlidingPuzzle.Parberry.LeftPlacement

/-! # Placement by distance

The placement words have lengths linear in the offsets of the tile from its
destination (`8d + 6v + c`), so a placement costs at most eight moves per unit
of grid distance between the tile and the destination (`exists_placement_dist`),
in addition to the uniform budget `8n` of `exists_placement`. -/
namespace SlidingPuzzle.Parberry
open Zhong
variable {n : ℕ}
local notation "c(" a "," b ")" => ((⟨a, by omega⟩ : Fin n), (⟨b, by omega⟩ : Fin n))

/-- Right-side placements cost at most `8` per unit of distance. -/
theorem exists_rightPlacementWord_dist (a b i j : ℕ)
    (ha : a+i < n) (hb : b+j+1 < n) (ha2 : a+2 < n) (hb2 : b+2 < n) :
    ∃ σ : List Dir, σ.length ≤ 8*(i+j) + 1 ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=c(a+i,b+j+1) ∧
      ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases hi : i=0
  · subst i
    cases j with
    | zero =>
        refine ⟨[.L],by simp,?_⟩
        simpa only [Nat.add_zero] using skipPlacementWord_spec a b (by omega : a+1 < n) (by omega)
    | succ v =>
        refine ⟨topPlacementWord a b v,by rw [topPlacementWord_length]; omega,?_⟩
        simpa only [Nat.add_zero,Nat.add_assoc] using topPlacementWord_spec a b v
          (by omega : a+1 < n) (by omega : b+v+2 < n)
  by_cases htall : j+2 ≤ i
  · let v := i-j-2
    have hx : a+v+j+2=a+i := by dsimp [v]; omega
    refine ⟨southeastPlacementWord a b j v,
      by rw [southeastPlacementWord_length]; dsimp [v]; omega,?_⟩
    simpa only [hx] using southeastPlacementWord_spec a b j v
      (by omega : a+v+j+2 < n) hb hb2
  by_cases hnear : i=j+1
  · cases j with
    | zero =>
        have hi1 : i=1 := by omega
        refine ⟨adjacentBelowWord,by simp [adjacentBelowWord]; omega,?_⟩
        simpa only [hi1,Nat.zero_add,Nat.add_zero] using adjacentBelowWord_spec a b ha2 hb2
    | succ d =>
        have hx : a+d+2=a+i := by omega
        have hy : b+(d+1)+1=b+d+2 := by omega
        refine ⟨nearPlacementWord a b d,by rw [nearPlacementWord_length]; omega,?_⟩
        simpa only [hx,hy] using nearPlacementWord_spec a b d (by omega : a+d+2 < n)
          (by omega : b+d+2 < n)
  by_cases heq : i=j
  · by_cases hj1 : j=1
    · have hi1 : i=1 := by omega
      refine ⟨adjacentDiagonalWord,by simp [adjacentDiagonalWord]; omega,?_⟩
      simpa only [hi1,hj1] using adjacentDiagonalWord_spec a b (by omega : a+1 < n) hb2
    · let d := j-2
      have hx : a+d+2=a+i := by dsimp [d]; omega
      have hy : b+d+3=b+j+1 := by dsimp [d]; omega
      refine ⟨equalPlacementWord a b d,by rw [equalPlacementWord_length]; dsimp [d]; omega,?_⟩
      simpa only [hx,hy] using equalPlacementWord_spec a b d (by omega : a+d+2 < n)
        (by omega : b+d+3 < n)
  · let d := i-1
    let v := j-i-1
    have hx : a+d+1=a+i := by dsimp [d]; omega
    have hy : b+v+d+3=b+j+1 := by dsimp [d,v]; omega
    refine ⟨widePlacementWord a b d v,by rw [widePlacementWord_length]; dsimp [d,v]; omega,?_⟩
    simpa only [hx,hy] using widePlacementWord_spec a b d v (by omega : a+d+1 < n)
      (by omega : b+v+d+3 < n)

/-- Left-side placements cost at most `8` per unit of distance. -/
theorem exists_leftPlacementWord_dist (a b i d : ℕ)
    (ha : a+i < n) (hi : 1 ≤ i) (hd : d ≤ b)
    (ha2 : a+2 < n) (hb2 : b+2 < n) (hne : i≠1 ∨ d≠0) :
    ∃ σ : List Dir, σ.length ≤ 8*(i+d+1) ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=c(a+i,b-d) ∧
      ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases htall : d+3 ≤ i
  · let v := i-d-3
    have hx : a+v+d+3=a+i := by dsimp [v]; omega
    refine ⟨westTallWord n a b d v,by rw [westTallWord_length n a b d v hd]; dsimp [v]; omega,?_⟩
    simpa only [hx] using westTallWord_spec a b d v (by omega : a+v+d+3 < n) hb2 hd
  by_cases hnear : i=d+2
  · have hx : a+d+2=a+i := by omega
    refine ⟨westNearWord a b d,by rw [westNearWord_length a b d hd]; omega,?_⟩
    simpa only [hx] using westNearWord_spec a b d (by omega : a+d+2 < n) hb2 hd
  · let e := i-1
    let v := d+1-i
    have he : v+e=d := by dsimp [v,e]; omega
    have hpos : 1 ≤ v+e := by omega
    have hx : a+e+1=a+i := by dsimp [e]; omega
    have hy : b-v-e=b-d := by omega
    refine ⟨westWideWord n a b e v,
      by rw [westWideWord_length n a b e v (by omega) hpos]; dsimp [e,v]; omega,?_⟩
    simpa only [hx,hy] using westWideWord_spec a b e v (by omega : a+e+1 < n)
      ha2 hb2 (by omega) hpos

/-- Complete placement word, at most `8` moves per unit of distance. -/
theorem exists_placementWord_dist (a b : ℕ) (x y : Fin n)
    (hfree : a<x.val ∨ (a=x.val ∧ b+1≤y.val))
    (ha2 : a+2 < n) (hb2 : b+2 < n) (hne : (x,y)≠c(a+1,b)) :
    ∃ σ : List Dir, σ.length ≤ 8*(x.val-a + y.val.dist (b+1)) + 1 ∧
      ApplicableFrom c(a+1,b) σ ∧ trace c(a+1,b) σ=c(a+1,b+1) ∧
      permOf c(a+1,b) σ c(a,b+1)=(x,y) ∧
      ∀ z : Zhong.Cell n n, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) →
        permOf c(a+1,b) σ z=z := by
  by_cases hy : b+1≤y.val
  · obtain ⟨σ,hlen,hs⟩ := exists_rightPlacementWord_dist a b (x.val-a) (y.val-b-1)
      (by omega : a+(x.val-a) < n) (by omega : b+(y.val-b-1)+1 < n) ha2 hb2
    have he : (c(a+(x.val-a),b+(y.val-b-1)+1) : Zhong.Cell n n)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    refine ⟨σ,?_,?_⟩
    · have : y.val.dist (b+1) = y.val-b-1 := by simp only [Nat.dist]; omega
      rw [this]; exact hlen
    · simpa only [he] using hs
  · have hni : x.val-a≠1 ∨ b-y.val≠0 := by
      by_contra hh
      apply hne
      apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    obtain ⟨σ,hlen,hs⟩ := exists_leftPlacementWord_dist a b (x.val-a) (b-y.val)
      (by omega : a+(x.val-a) < n) (by omega) (by omega) ha2 hb2 hni
    have he : (c(a+(x.val-a),b-(b-y.val)) : Zhong.Cell n n)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    refine ⟨σ,?_,?_⟩
    · have : y.val.dist (b+1) = b-y.val+1 := by simp only [Nat.dist]; omega
      rw [this]; omega
    · simpa only [he] using hs

/-- A legal placement costing at most `8` moves per unit of distance between the
tile and its destination `(a, b+1)`. -/
theorem exists_placement_dist [NeZero n] (B : Board n) (a b : ℕ) (x y : Fin n)
    (hfree : a<x.val ∨ (a=x.val ∧ b+1≤y.val))
    (hne : (x,y)≠blank B) (ha2 : a+2 < n) (hb2 : b+2 < n)
    (hblank : blank B=c(a+1,b)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ 8*gridDistance (x,y) c(a,b+1) + 1 ∧ blank C=c(a+1,b+1) ∧
      C c(a,b+1)=B (x,y) ∧
      ∀ z, z.1.val<a ∨ (z.1.val=a ∧ z.2.val<b+1) → C z=B z := by
  obtain ⟨σ,hlen,_,ht,hp,hfix⟩ := exists_placementWord_dist a b x y hfree ha2 hb2
    (by simpa only [← hblank] using hne)
  obtain ⟨p,hle⟩ := path_of_zhong_word B σ
  refine ⟨Zhong.actSeq B σ,p,?_,?_,?_,?_⟩
  · have : x.val-a + y.val.dist (b+1) = gridDistance (x,y) c(a,b+1) := by
      simp only [gridDistance, Nat.dist]; omega
    omega
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
