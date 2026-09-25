import SlidingPuzzle.Algorithm.Cardinalities
import SlidingPuzzle.Moves.BulkExchangeSchedule

/-! Arrangement's first schedule: exchange V(i,j) with V(j,i). -/
namespace SlidingPuzzle.Partition
variable {n k : ℕ} [NeZero n]

omit [NeZero n] in
/-- The diagonal group pairs already belong to their containing square. -/
theorem card_vertical_active :
    ((Finset.univ : Finset (GroupIndex k × GroupIndex k)).filter
      (fun i => i.swap ≠ i)).card = k^4-k^2 := by
  have hfixed : ((Finset.univ : Finset (GroupIndex k × GroupIndex k)).filter
      (fun i => i.swap = i)).card = k*k := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp [Prod.ext_iff, eq_comm]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (GroupIndex k × GroupIndex k))) (fun i => i.swap = i)
  rw [hfixed] at h
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  calc
    _ = k*k*(k*k)-k*k := Nat.eq_sub_of_add_eq' h
    _ = k^4-k^2 := by congr 1 <;> ring

/-- Every vertical corridor can be put in its own square's group, with horizontal
corridors and reservoirs restored exactly. -/
theorem exists_vertical_arrangement_path (hk : Dims n k) (B : Board n)
    (hclear : Clear (k := k) B) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ (24*(side n k-k)+2032)*(k^4-k^2)*n ∧ blank C = blank B ∧
      (∀ (i j : GroupIndex k) x, vertical i j x → C x ∈ targetGroup i) ∧
      (∀ (i : GroupIndex k) x, horizontal i x → C x = B x) ∧
      (∀ (i : GroupIndex k) x, reservoir i x → C x = B x) := by
  classical
  have hn : 4 ≤ n := hk.two_le_n
  have hk3 : 2 ≤ side n k-k := by have := hk.k_add_two_le; omega
  let S : GroupIndex k × GroupIndex k → Finset (Cell n) := fun ij => verticalCells ij.1 ij.2
  have hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hh := vertical_unique hk (mem_verticalCells _ _ _ |>.mp hxi)
      (mem_verticalCells _ _ _ |>.mp hxj)
    exact hij (Prod.ext hh.1 hh.2)
  have hsize : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ side n k-k := by
    intro i
    dsimp [S]
    rw [card_vertical hk]
    exact ⟨hk3,le_rfl⟩
  have hcard : ∀ i, (S i).card = (S i.swap).card := by
    intro i
    dsimp [S]
    rw [card_vertical hk,card_vertical hk]
  have hzero : ∀ i x, x ∈ S i → B x ≠ 0 := by
    intro i x hx hz
    have hh := hclear.2 i.1 i.2 x (mem_verticalCells _ _ _ |>.mp hx)
    exact zero_not_mem_targetGroup i.2 (hz ▸ hh)
  obtain ⟨C,p,hp,hbC,hC,hfix⟩ := exists_bulk_involution_region_path_active B hn S Prod.swap
    (fun _ => rfl) hdis (side n k-k) (by
      have hh := Nat.mul_le_mul_right (side n k) hk.two_le
      have he := hk.mul_side
      omega) hsize hcard hzero
    (fun i t => t ∈ targetGroup i.1) Finset.univ (by simp)
    (by intro i _ x hx; exact hclear.2 i.1 i.2 x (mem_verticalCells _ _ _ |>.mp hx))
  refine ⟨C,p,?_,hbC,?_,?_,?_⟩
  · simpa only [card_vertical_active] using hp
  · intro i j x hx
    exact hC (i,j) (Finset.mem_univ _) x (mem_verticalCells _ _ _ |>.mpr hx)
  · intro i x hx
    apply hfix
    intro j _ hj
    exact horizontal_not_vertical hk hx (mem_verticalCells _ _ _ |>.mp hj)
  · intro i x hx
    apply hfix
    intro j _ hj
    exact vertical_not_reservoir hk (mem_verticalCells _ _ _ |>.mp hj) hx
end SlidingPuzzle.Partition
