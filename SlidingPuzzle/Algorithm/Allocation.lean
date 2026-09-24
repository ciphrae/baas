import SlidingPuzzle.Algorithm.Cardinalities
import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Algorithm.Dimension

/-! Finite tile allocations extend to a complete target board. -/
namespace SlidingPuzzle
noncomputable section
open Classical
variable {n : ℕ} [NeZero n]

/-- An injective family of nonblank labels can be prescribed at any injective
family of cells away from the standard blank. -/
theorem exists_board_extending_cell_embedding {α : Type*} [Fintype α]
    (u : α ↪ Cell n) (f : α ↪ Tile n)
    (hu0 : ∀ i, target n (u i) ≠ 0) (hf0 : ∀ i, f i ≠ 0) :
    ∃ T : Board n, blank T = blank (target n) ∧ ∀ i, T (u i) = f i := by
  let a : Option α → Tile n
    | none => 0
    | some i => target n (u i)
  let b : Option α → Tile n
    | none => 0
    | some i => f i
  have ha : Function.Injective a := by
    intro i j h
    cases i with
    | none => cases j with
      | none => rfl
      | some j => exact False.elim (hu0 j h.symm)
    | some i => cases j with
      | none => exact False.elim (hu0 i h)
      | some j => exact congrArg some (u.injective ((target n).injective h))
  have hb : Function.Injective b := by
    intro i j h
    cases i with
    | none => cases j with
      | none => rfl
      | some j => exact False.elim (hf0 j h.symm)
    | some i => cases j with
      | none => exact False.elim (hf0 i h)
      | some j => exact congrArg some (f.injective h)
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  exact ⟨relabel (target n) e, blank_relabel _ e (he none), fun i => he (some i)⟩

/-- Any injective nonblank assignment away from the target blank extends to a board
with its blank in the standard position. -/
theorem exists_board_extending_assignment (s : Finset (Cell n))
    (hb : blank (target n) ∉ s) (f : {c // c ∈ s} ↪ Tile n)
    (hf : ∀ c, f c ≠ 0) :
    ∃ T : Board n, blank T = blank (target n) ∧ ∀ c, T c.val=f c := by
  let u : Option {c // c ∈ s} → Tile n
    | none => 0
    | some c => target n c.val
  let v : Option {c // c ∈ s} → Tile n
    | none => 0
    | some c => f c
  have hnonzero (c : {c // c ∈ s}) : target n c.val ≠ 0 := by
    intro h
    have he : c.val = blank (target n) := (target n).injective
      (h.trans ((target n).apply_symm_apply 0).symm)
    exact hb (he ▸ c.property)
  have hu : Function.Injective u := by
    intro a b h
    cases a with
    | none => cases b with
      | none => rfl
      | some b => exact False.elim (hnonzero b h.symm)
    | some a => cases b with
      | none => exact False.elim (hnonzero a h)
      | some b => exact congrArg some (Subtype.ext ((target n).injective h))
  have hv : Function.Injective v := by
    intro a b h
    cases a with
    | none => cases b with
      | none => rfl
      | some b => exact False.elim (hf b h.symm)
    | some a => cases b with
      | none => exact False.elim (hf a h)
      | some b => exact congrArg some (f.injective h)
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair u v hu hv
  refine ⟨relabel (target n) e,blank_relabel _ e (he none),?_⟩
  intro c
  exact he (some c)

/-- Group-size inequalities suffice to fill any prescribed finite set of cells;
there is no additional tile-availability hypothesis. -/
theorem exists_board_with_group_assignment {k : ℕ} (hk : 2 ≤ k)
    (s : Finset (Cell n)) (hb : blank (target n) ∉ s)
    (required : {c // c ∈ s} → Partition.GroupIndex k)
    (hcapacity : ∀ i, Fintype.card {c : {c // c ∈ s} // required c=i} ≤
      (Partition.targetGroup (n := n) i).card) :
    ∃ T : Board n, blank T = blank (target n) ∧
      ∀ c : {c // c ∈ s}, T c.val ∈ Partition.targetGroup (required c) := by
  have he (i : Partition.GroupIndex k) : Nonempty
      ({c : {c // c ∈ s} // required c=i} ↪ {t // t ∈ Partition.targetGroup (n := n) i}) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hcapacity i)
  let e := fun i => Classical.choice (he i)
  let f : {c // c ∈ s} → Tile n := fun c => (e (required c) ⟨c,rfl⟩).val
  have hmem (c : {c // c ∈ s}) : f c ∈ Partition.targetGroup (required c) :=
    (e (required c) ⟨c,rfl⟩).property
  have huniq (i j : Partition.GroupIndex k)
      (a : {c : {c // c ∈ s} // required c=i})
      (b : {c : {c // c ∈ s} // required c=j})
      (h : (e i a).val=(e j b).val) : a.val=b.val := by
    have hij : i=j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (Partition.targetGroups_disjoint hk hne))
        (e i a).property (h ▸ (e j b).property)
    subst j
    exact congrArg Subtype.val ((e i).injective (Subtype.ext h))
  have hinj : Function.Injective f := by
    intro a b h
    exact huniq (required a) (required b) ⟨a,rfl⟩ ⟨b,rfl⟩ h
  have hf : ∀ c, f c ≠ 0 := by
    intro c hz
    exact Partition.zero_not_mem_targetGroup (required c) (hz ▸ hmem c)
  obtain ⟨T,hT,hfT⟩ := exists_board_extending_assignment s hb ⟨f,hinj⟩ hf
  refine ⟨T,hT,?_⟩
  intro c
  rw [hfT c]
  exact hmem c

/- Place prescribed groups in an outer prefix using only the finite capacity
inequalities. The completed target board is constructed inside this theorem. -/
end
end SlidingPuzzle
