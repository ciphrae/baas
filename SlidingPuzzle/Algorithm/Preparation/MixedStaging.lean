import SlidingPuzzle.Algorithm.Allocation
import SlidingPuzzle.Algorithm.Preparation.Representatives
import SlidingPuzzle.Parberry.MixedPrefix

/-! Staging with a mixed prefix. The compressed staging quotas lie in the first
`k³` columns or the first `k²` rows, and the representatives lie in row `k²`.
Solving `k³` columns and `k²+1` rows costs about `7.5*k³n²` moves; solving `k³`
complete layers would cost twice as much. -/
namespace SlidingPuzzle
noncomputable section
open Classical

section
variable {n : ℕ} [NeZero n]

theorem exists_mixed_group_path {k : ℕ} (hk : Partition.Dims n k) (B : Board n) (hn : 4 ≤ n)
    (r d : ℕ) (hd : d+4 ≤ n) (hr : r+2 ≤ n) (s : Finset (Cell n))
    (hs : ∀ c ∈ s, c.1.val<r ∨ c.2.val<d)
    (required : {c // c ∈ s} → Partition.GroupIndex k)
    (hcapacity : ∀ i, Fintype.card {c : {c // c ∈ s} // required c=i} ≤
      (Partition.targetGroup (n := n) i).card) :
    ∃ C : Board n, ∃ p : Path B C, 2*p.length ≤ (d+r)*(15*n^2+3002*n+1) ∧
      (∀ c : {c // c ∈ s}, C c.val ∈ Partition.targetGroup (required c)) ∧
      r ≤ (blank C).1.val ∧ d ≤ (blank C).2.val := by
  have hb : blank (target n) ∉ s := by
    intro h
    have hh := hs _ h
    have he : blank (target n) =
        (⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩,
         ⟨n-1, Nat.sub_lt (NeZero.pos n) (by omega)⟩) := by
      apply (target n).injective
      rw [target_bottomRight]
      exact (target n).apply_symm_apply 0
    rw [he] at hh
    simp only at hh
    omega
  obtain ⟨T,hT,hassign⟩ := exists_board_with_group_assignment hk s hb required hcapacity
  obtain ⟨C,p,hp,hC⟩ := Parberry.exists_mixed_prefix B T hT hn r d hd hr
  refine ⟨C,p,hp,?_,?_⟩
  · intro c
    have he := hC c.val.1 c.val.2 (hs c.val c.property)
    change C c.val=T c.val at he
    rw [he]
    exact hassign c
  · have hnot : ¬ ((blank C).1.val < r ∨ (blank C).2.val < d) := by
      intro h
      have he : blank C = blank T := T.injective (by
        rw [← hC (blank C).1 (blank C).2 h]
        simp [blank, position])
      rw [he, hT] at h
      have ht : blank (target n) =
          (⟨n-1, by have := NeZero.pos n; omega⟩,
           ⟨n-1, by have := NeZero.pos n; omega⟩) := by
        apply (target n).injective
        rw [target_bottomRight]
        simp [blank, position]
      rw [ht] at h
      simp only at h
      omega
    omega

theorem exists_mixed_disjoint_group_path {k : ℕ} (hk : Partition.Dims n k) (B : Board n) (hn : 4 ≤ n)
    (r d : ℕ) (hd : d+4 ≤ n) (hr : r+2 ≤ n) (s : Partition.GroupIndex k → Finset (Cell n))
    (hdisjoint : (Set.univ : Set (Partition.GroupIndex k)).PairwiseDisjoint s)
    (hprefix : ∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
      c.1.val < r ∨ c.2.val < d)
    (hcapacity : ∀ i : Partition.GroupIndex k,
      (s i).card ≤ (Partition.targetGroup (n := n) i).card) :
    ∃ C : Board n, ∃ p : Path B C, 2*p.length ≤ (d+r)*(15*n^2+3002*n+1) ∧
      (∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
        C c ∈ Partition.targetGroup i) ∧
      r ≤ (blank C).1.val ∧ d ≤ (blank C).2.val := by
  let u : Finset (Cell n) := Finset.univ.biUnion s
  have hu (c : Cell n) : c ∈ u ↔ ∃ i : Partition.GroupIndex k, c ∈ s i := by
    simp [u]
  let required : {c // c ∈ u} → Partition.GroupIndex k := fun c =>
    Classical.choose (show ∃ i : Partition.GroupIndex k, c.val ∈ s i from (hu c.val).mp c.property)
  have hrequired (c : {c // c ∈ u}) : c.val ∈ s (required c) := by
    exact Classical.choose_spec
      (show ∃ i : Partition.GroupIndex k, c.val ∈ s i from (hu c.val).mp c.property)
  have hfib (i : Partition.GroupIndex k) :
      Fintype.card {c : {c // c ∈ u} // required c = i} ≤ (s i).card := by
    let e : {c : {c // c ∈ u} // required c = i} ↪ {c // c ∈ s i} :=
      { toFun := fun c => ⟨c.val.val, by
          have hi : c.val.val ∈ s (required c.val) := hrequired c.val
          rw [c.property] at hi
          exact hi⟩,
        inj' := by
          intro a b h
          have hv : a.val.val = b.val.val :=
            congrArg (fun z : {c // c ∈ s i} => z.val) h
          apply Subtype.ext
          apply Subtype.ext
          exact hv }
    calc
      Fintype.card {c : {c // c ∈ u} // required c = i} ≤
          Fintype.card {c // c ∈ s i} := Fintype.card_le_of_injective e e.injective
      _ = (s i).card := Fintype.card_coe (s i)
  have huprefix : ∀ c : Cell n, c ∈ u → c.1.val < r ∨ c.2.val < d := by
    intro c hc
    obtain ⟨i, hi⟩ := (hu c).mp hc
    exact hprefix i c hi
  obtain ⟨C, p, hp, hC, hb⟩ := exists_mixed_group_path hk B hn r d hd hr u huprefix required (by
    intro i
    exact (hfib i).trans (hcapacity i))
  refine ⟨C, p, hp, ?_, hb⟩
  intro i c hci
  have hcu : c ∈ u := (hu c).mpr ⟨i, hci⟩
  have hreq : required ⟨c, hcu⟩ = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp
      (hdisjoint (Set.mem_univ _) (Set.mem_univ _) hne))
      (hrequired ⟨c, hcu⟩) hci
  simpa [hreq] using hC ⟨c, hcu⟩


end

namespace Partition

theorem representativeStaging_mixed {n k : ℕ} (hk : Dims n k) [NeZero n] :
    RepresentativeStaging hk ((k^3+(k^2+1))*(15*n^2+3002*n+1)) := by
  intro B
  have hg := preparation_geometry hk
  obtain ⟨C,p,hp,hC,hb⟩ := exists_mixed_disjoint_group_path hk B (by omega) (k^2+1) (k^3)
    (by omega) (by omega) (representativeStagingCells hk) (representativeStagingCells_disjoint hk)
    (by
      intro i c hc
      rcases (mem_representativeStagingCells hk i c).mp hc with hc | ⟨_,rfl⟩
      · rcases stagingCells_compressed hk hc with h | h
        · left; omega
        · right; exact h
      · left; change k^2 < k^2+1; omega)
    (representativeStagingCells_capacity hk)
  refine ⟨C,p,hp,?_,?_,hb⟩
  · intro i c hc
    exact hC i c ((mem_representativeStagingCells hk i c).mpr (Or.inl hc))
  · intro i hi
    exact hC i _ ((mem_representativeStagingCells hk i _).mpr (Or.inr ⟨hi,rfl⟩))

end Partition
end
end SlidingPuzzle
