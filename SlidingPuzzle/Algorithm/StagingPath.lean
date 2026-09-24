import SlidingPuzzle.Algorithm.Allocation
import SlidingPuzzle.Algorithm.PreparationCapacity
import SlidingPuzzle.Algorithm.Staging

/-! A legal path which fills a finite family of disjoint group quotas. -/
namespace SlidingPuzzle

noncomputable section
open Classical

variable {n : ℕ} [NeZero n]

/- A family of pairwise disjoint cell quotas can be filled simultaneously by one
prefix path.  The family is indexed by the target groups, so that each quota
has its own capacity bound. -/
/-- Disjoint group quotas inherit any protected-prefix cost. -/
theorem exists_prefix_disjoint_group_path_with_blank_of_bound {P k : ℕ}
    (hpath : PrefixPathBound P) (hk : 2 ≤ k) (B : Board n)
    (d : ℕ) (hd : d + 4 ≤ n) (s : Partition.GroupIndex k → Finset (Cell n))
    (hdisjoint : (Set.univ : Set (Partition.GroupIndex k)).PairwiseDisjoint s)
    (hprefix : ∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
      c.1.val < d ∨ c.2.val < d)
    (hcapacity : ∀ i : Partition.GroupIndex k,
      (s i).card ≤ (Partition.targetGroup (n := n) i).card) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ P*d*n^2 ∧
      (∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
        C c ∈ Partition.targetGroup i) ∧
      d ≤ (blank C).1.val ∧ d ≤ (blank C).2.val := by
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
  have huprefix : ∀ c : Cell n, c ∈ u → c.1.val < d ∨ c.2.val < d := by
    intro c hc
    obtain ⟨i, hi⟩ := (hu c).mp hc
    exact hprefix i c hi
  obtain ⟨C, p, hp, hC, hb⟩ := exists_prefix_group_path_with_blank_of_bound hpath hk B d hd u huprefix required (by
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

theorem exists_prefix_disjoint_group_path_with_blank {k : ℕ} (hk : 2 ≤ k) (B : Board n)
    (d : ℕ) (hd : d + 4 ≤ n) (s : Partition.GroupIndex k → Finset (Cell n))
    (hdisjoint : (Set.univ : Set (Partition.GroupIndex k)).PairwiseDisjoint s)
    (hprefix : ∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
      c.1.val < d ∨ c.2.val < d)
    (hcapacity : ∀ i : Partition.GroupIndex k,
      (s i).card ≤ (Partition.targetGroup (n := n) i).card) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ 1004*d*n^2 ∧
      (∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
        C c ∈ Partition.targetGroup i) ∧
      d ≤ (blank C).1.val ∧ d ≤ (blank C).2.val := by
  exact exists_prefix_disjoint_group_path_with_blank_of_bound prefixPathBound_current hk B d hd s hdisjoint hprefix hcapacity

/-- Disjoint prefix quotas can be filled without retaining the blank-location
conclusion in the interface. -/
theorem exists_prefix_disjoint_group_path {k : ℕ} (hk : 2 ≤ k) (B : Board n)
    (d : ℕ) (hd : d + 4 ≤ n) (s : Partition.GroupIndex k → Finset (Cell n))
    (hdisjoint : (Set.univ : Set (Partition.GroupIndex k)).PairwiseDisjoint s)
    (hprefix : ∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
      c.1.val < d ∨ c.2.val < d)
    (hcapacity : ∀ i : Partition.GroupIndex k,
      (s i).card ≤ (Partition.targetGroup (n := n) i).card) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ 1004*d*n^2 ∧
      ∀ (i : Partition.GroupIndex k) (c : Cell n), c ∈ s i →
        C c ∈ Partition.targetGroup i := by
  obtain ⟨C,p,hp,hC,_⟩ := exists_prefix_disjoint_group_path_with_blank
    hk B d hd s hdisjoint hprefix hcapacity
  exact ⟨C,p,hp,hC⟩

/-- The compressed staging quotas admit a legal path of the required
fourth-power length. -/
theorem exists_staging_path {k : ℕ} (hk : 2 ≤ k) (B : Board (k^4)) :
    letI : NeZero (k^4) := ⟨by positivity⟩
    ∃ C : Board (k^4), ∃ p : Path B C, p.length ≤ 1004*k^11 ∧
      ∀ (i : Partition.GroupIndex k) (c : Cell (k^4)),
        c ∈ Partition.stagingCells i → C c ∈ Partition.targetGroup i := by
  let : NeZero (k^4) := ⟨by positivity⟩
  have hk3 : 4 ≤ k^3 := by nlinarith [show 0 ≤ k^2 by positivity]
  have hprefix : k^3 + 4 ≤ k^4 := by
    calc
      k^3 + 4 ≤ 2*k^3 := by omega
      _ ≤ k*k^3 := Nat.mul_le_mul_right _ hk
      _ = k^4 := by ring
  obtain ⟨C, p, hp, hC⟩ := exists_prefix_disjoint_group_path hk B (k^3) hprefix
    (Partition.stagingCells (n := k^4))
    (Partition.stagingCells_pairwise_disjoint hk)
    (by
      intro i c hc
      exact Partition.stagingCells_prefix hk hc)
    (by
      intro i
      rw [Partition.card_stagingCells hk rfl i]
      exact Partition.card_targetGroup_ge_corridor_quota hk rfl i)
  refine ⟨C, p, ?_, hC⟩
  calc
    p.length ≤ 1004 * k^3 * (k^4)^2 := hp
    _ = 1004*k^11 := by ring

end
end SlidingPuzzle
