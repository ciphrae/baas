import SlidingPuzzle.Algorithm.Cardinalities
import SlidingPuzzle.Moves.BulkExchangeSchedule
import SlidingPuzzle.Moves.FamilySwap
import SlidingPuzzle.Algorithm.Arrangement.Cost

/-! Arrangement's first schedule: exchange V(i,j) with V(j,i), moving one family
next to the other (`Moves/FamilySwap.lean`). -/
namespace SlidingPuzzle.Partition
variable {n k : ℕ} [NeZero n]

/-- The column of the vertical corridor `V(i,j)`. -/
def vcol (n k : ℕ) (ij : GroupIndex k × GroupIndex k) : ℕ :=
  (groupCol ij.1).val*side n k+ij.2.val

/-- The top row of the vertical corridor `V(i,j)`. -/
def vrow (n k : ℕ) (ij : GroupIndex k × GroupIndex k) : ℕ :=
  (groupRow ij.1).val*side n k+2*k

/-- The budget of one side of the exchange `V(i,j) ↔ V(j,i)`. -/
def vcost (n k : ℕ) (ij : GroupIndex k × GroupIndex k) : ℕ :=
  4*n+Nat.dist (vcol n k ij) (vcol n k ij.swap)*(6*(side n k-2*k)+5)+
    Nat.dist (vrow n k ij) (vrow n k ij.swap)*(2*(side n k-2*k)+3)+3*(side n k-2*k)+1

private theorem mul_gap {a b s : ℕ} (h : a < b) : a*s+s ≤ b*s := by
  have := Nat.mul_le_mul_right s (show a+1 ≤ b by omega)
  simpa [Nat.add_mul] using this

omit [NeZero n] in
private theorem mem_vertical_param (hk : Dims n k) (ij : GroupIndex k × GroupIndex k)
    (x : Cell n) (hx : vertical ij.1 ij.2 x) :
    ∃ t, ∃ ht : t < side n k-2*k,
      x = (⟨vrow n k ij+t, by
        have := hk.k_add_two_le; have h := block_end_le hk (groupRow ij.1)
        simp only [vrow, Nat.add_mul, Nat.one_mul] at *; omega⟩,
        ⟨vcol n k ij, by simp only [vcol]; rw [← hx.2.2]; exact x.2.isLt⟩) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨x.1.val-vrow n k ij, ?_, ?_⟩
  · simp only [vrow, Nat.add_mul, Nat.one_mul] at *; omega
  · apply Prod.ext <;> apply Fin.ext
    · simp only [vrow] at *; omega
    · simp only [vcol]; exact h3

omit [NeZero n] in
private theorem vertical_of_param (hk : Dims n k) (ij : GroupIndex k × GroupIndex k)
    (t : ℕ) (ht : t < side n k-2*k) (h1 : vrow n k ij+t < n) (h2 : vcol n k ij < n) :
    vertical ij.1 ij.2 ((⟨vrow n k ij+t, h1⟩, ⟨vcol n k ij, h2⟩) : Cell n) := by
  refine ⟨?_, ?_, rfl⟩ <;> simp only [vrow, Nat.add_mul, Nat.one_mul] at * <;> omega

/-- Arrangement's first schedule by moving one family next to the other:
exchange `V(i,j)` with `V(j,i)` at a cost reflecting their distance. -/
theorem exists_vertical_arrangement_path_near (hk : Dims n k) (B : Board n)
    (hclear : Clear (k := k) B) (hblank : ∃ g : GroupIndex k, reservoir g (blank B)) :
    ∃ C : Board n, ∃ p : Path B C,
      p.length ≤ ∑ ij ∈ Finset.univ.filter (fun ij : GroupIndex k × GroupIndex k => ij.swap ≠ ij),
        vcost n k ij ∧ blank C = blank B ∧
      (∀ (i j : GroupIndex k) x, vertical i j x → C x ∈ targetGroup i) ∧
      (∀ (i : GroupIndex k) x, horizontal i x → C x = B x) ∧
      (∀ (i : GroupIndex k) x, reservoir i x → C x = B x) := by
  classical
  obtain ⟨hk2, hk2', hk3, hks, hkn⟩ := hk.facts
  have hsq := hk.sq_add_le
  have hkk := hk.k_add_two_le
  have h2k : 2*k+2 ≤ side n k := by nlinarith
  set m := side n k-2*k with hmdef
  let S : GroupIndex k × GroupIndex k → Finset (Cell n) := fun ij => verticalCells ij.1 ij.2
  have hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hh := vertical_unique hk (mem_verticalCells _ _ _ |>.mp hxi)
      (mem_verticalCells _ _ _ |>.mp hxj)
    exact hij (Prod.ext hh.1 hh.2)
  obtain ⟨g, hg⟩ := hblank
  have hcolv : ∀ x : GroupIndex k, ((groupCol x).val : ℕ) = x.val % k := by intro x; simp [groupCol]
  have hcolk : ∀ x : GroupIndex k, (groupCol x).val < k := fun x => (groupCol x).isLt
  have hrowk : ∀ x : GroupIndex k, (groupRow x).val < k := fun x => (groupRow x).isLt
  have hidx : ∀ x : GroupIndex k, x.val < k^2 := fun x => by simpa [pow_two] using x.isLt
  have hexchange : ∀ ij, ij.swap ≠ ij → ∀ D : Board n, blank D = blank B →
      ∀ (P Q : Tile n → Prop), (∀ x ∈ S ij, P (D x)) → (∀ x ∈ S ij.swap, Q (D x)) →
      ∃ C : Board n, ∃ p : Path D C,
        p.length ≤ vcost n k ij+vcost n k ij.swap ∧ blank C = blank D ∧
        (∀ x ∈ S ij, Q (C x)) ∧ (∀ x ∈ S ij.swap, P (C x)) ∧
        ∀ x, x ∉ S ij → x ∉ S ij.swap → C x = D x := by
    rintro ⟨i, j⟩ hij D hD P Q hP hQ
    have hij' : i ≠ j := fun h => hij (by simp [h])
    have hiv := hidx i; have hjv := hidx j
    have hci := hcolk i; have hcj := hcolk j; have hri := hrowk i; have hrj := hrowk j
    have hbi := block_end_le hk (groupCol i); have hbj := block_end_le hk (groupCol j)
    have hri' := block_end_le hk (groupRow i); have hrj' := block_end_le hk (groupRow j)
    simp only [Nat.add_mul, Nat.one_mul] at hbi hbj hri' hrj'
    set c₁ := vcol n k (i, j) with hc₁d
    set c₂ := vcol n k (j, i) with hc₂d
    set r₁ := vrow n k (i, j) with hr₁d
    set r₂ := vrow n k (j, i) with hr₂d
    have hc₁ : c₁ = (groupCol i).val*side n k+j.val := by rw [hc₁d]; rfl
    have hc₂ : c₂ = (groupCol j).val*side n k+i.val := by rw [hc₂d]; rfl
    have hr₁ : r₁ = (groupRow i).val*side n k+2*k := by rw [hr₁d]; rfl
    have hr₂ : r₂ = (groupRow j).val*side n k+2*k := by rw [hr₂d]; rfl
    -- Column facts.
    have hgap : ∀ a b : Fin k, a.val < b.val → a.val*side n k+side n k ≤ b.val*side n k :=
      fun a b h => mul_gap h
    have hne : c₁ ≠ c₂ := by
      rcases lt_trichotomy (groupCol i).val (groupCol j).val with h | h | h
      · have := hgap _ _ h; omega
      · intro he
        rw [hc₁, hc₂, h] at he
        exact hij' (Fin.ext (by omega))
      · have := hgap _ _ h; omega
    have hmax : 2 ≤ max c₁ c₂ := by
      by_contra hlt
      have h1 : c₁ ≤ 1 := by omega
      have h2 : c₂ ≤ 1 := by omega
      have hgi : (groupCol i).val = 0 := by
        by_contra h0
        have := Nat.mul_le_mul_right (side n k) (show 1 ≤ (groupCol i).val by omega)
        omega
      have hgj : (groupCol j).val = 0 := by
        by_contra h0
        have := Nat.mul_le_mul_right (side n k) (show 1 ≤ (groupCol j).val by omega)
        omega
      rw [hgi, zero_mul, zero_add] at hc₁; rw [hgj, zero_mul, zero_add] at hc₂
      rw [hcolv] at hgi hgj
      have hi1 : i.val ≤ 1 := by omega
      have hj1 : j.val ≤ 1 := by omega
      have : i.val ≠ j.val := fun h => hij' (Fin.ext h)
      rcases (show i.val = 1 ∨ j.val = 1 by omega) with h | h
      · rw [h, Nat.mod_eq_of_lt (by omega)] at hgi; omega
      · rw [h, Nat.mod_eq_of_lt (by omega)] at hgj; omega
    have hcn : max c₁ c₂+2 ≤ n := by
      have h1 : c₁+2 ≤ n := by
        rw [hc₁]
        have := Nat.mul_le_mul_right (side n k) (show (groupCol i).val+1 ≤ k by omega)
        rw [Nat.add_mul, Nat.one_mul, hk.mul_side] at this; omega
      have h2 : c₂+2 ≤ n := by
        rw [hc₂]
        have := Nat.mul_le_mul_right (side n k) (show (groupCol j).val+1 ≤ k by omega)
        rw [Nat.add_mul, Nat.one_mul, hk.mul_side] at this; omega
      omega
    have hpark : ∀ t, t < m → r₂+t+1 ≠ r₁ ∧ r₁+t+1 ≠ r₂ := by
      intro t ht
      rcases lt_trichotomy (groupRow i).val (groupRow j).val with h | h | h
      · have := hgap _ _ h; constructor <;> omega
      · rw [hr₁, hr₂, h]; constructor <;> omega
      · have := hgap _ _ h; constructor <;> omega
    have hcol : (blank D).2.val ≠ c₁ ∧ (blank D).2.val ≠ c₂ := by
      rw [hD]
      obtain ⟨-, -, hg3, hg4⟩ := hg
      simp only [Nat.add_mul, Nat.one_mul] at hg4
      have hgc := hcolk g
      constructor
      · rcases lt_trichotomy (groupCol g).val (groupCol i).val with h | h | h
        · have := hgap _ _ h; omega
        · rw [hc₁, ← h]; omega
        · have := hgap _ _ h; omega
      · rcases lt_trichotomy (groupCol g).val (groupCol j).val with h | h | h
        · have := hgap _ _ h; omega
        · rw [hc₂, ← h]; omega
        · have := hgap _ _ h; omega
    obtain ⟨C, p, hp, hbC, h1, h2, hfix⟩ := exists_column_family_swap D c₁ c₂ r₁ r₂ m
      (by omega) hne hmax hcn (by omega) (by omega) (by omega) (by omega) hpark hcol
    refine ⟨C, p, ?_, hbC, ?_, ?_, ?_⟩
    · have hsym : vcost n k (j, i) = vcost n k (i, j) := by
        simp only [vcost, Prod.swap, Nat.dist_comm (vcol n k (j, i)),
          Nat.dist_comm (vrow n k (j, i))]
      simp only [Prod.swap] at hsym ⊢
      rw [hsym]
      simp only [vcost, Prod.swap]
      rw [← hc₁d, ← hc₂d, ← hr₁d, ← hr₂d]
      simp only [← hmdef]
      have := Nat.mul_le_mul_right (6*m+5) (Nat.sub_le (Nat.dist c₁ c₂) 1)
      omega
    · intro x hx
      obtain ⟨t, ht, hxe⟩ := mem_vertical_param hk (i, j) x ((mem_verticalCells _ _ _).mp hx)
      obtain ⟨j', hj', he⟩ := h1 t ht
      rw [hxe, he]
      apply hQ
      exact (mem_verticalCells _ _ _).mpr (vertical_of_param hk (j, i) j' hj' _ _)
    · intro x hx
      obtain ⟨t, ht, hxe⟩ := mem_vertical_param hk (j, i) x ((mem_verticalCells _ _ _).mp hx)
      obtain ⟨j', hj', he⟩ := h2 t ht
      rw [hxe, he]
      apply hP
      exact (mem_verticalCells _ _ _).mpr (vertical_of_param hk (i, j) j' hj' _ _)
    · intro x hx1 hx2
      apply hfix
      · intro t ht he
        exact hx1 (he ▸ (mem_verticalCells _ _ _).mpr (vertical_of_param hk (i, j) t ht _ _))
      · intro t ht he
        exact hx2 (he ▸ (mem_verticalCells _ _ _).mpr (vertical_of_param hk (j, i) t ht _ _))
  obtain ⟨C, p, hp, hbC, hC, hfix⟩ := exists_involution_region_path_of_pair_exchange B S Prod.swap
    (fun _ => rfl) hdis (vcost n k) hexchange (fun i t => t ∈ targetGroup i.1) Finset.univ
    (by simp)
    (by intro i _ x hx; exact hclear.2 i.1 i.2 x (mem_verticalCells _ _ _ |>.mp hx))
  refine ⟨C, p, hp, hbC, ?_, ?_, ?_⟩
  · intro i j x hx
    exact hC (i, j) (Finset.mem_univ _) x (mem_verticalCells _ _ _ |>.mpr hx)
  · intro i x hx
    apply hfix
    intro j _ hj
    exact horizontal_not_vertical hk hx (mem_verticalCells _ _ _ |>.mp hj)
  · intro i x hx
    apply hfix
    intro j _ hj
    exact vertical_not_reservoir hk (mem_verticalCells _ _ _ |>.mp hj) hx

omit [NeZero n] in
/-- The vertical exchanges cost `(8/3)*k⁵s² + O(k*s³)` in total. -/
theorem sum_vcost_le (hk : Dims n k) :
    3*∑ ij ∈ Finset.univ.filter (fun ij : GroupIndex k × GroupIndex k => ij.swap ≠ ij),
      vcost n k ij ≤ 8*(k^5*side n k^2)+66*(k*side n k^3) := by
  classical
  obtain ⟨hk2, hk2', hk3, hks, hkn⟩ := hk.facts
  set s := side n k with hsdef
  set m := s-2*k with hm
  have hms : m ≤ s := Nat.sub_le _ _
  have hidx : ∀ x : GroupIndex k, x.val < k^2 := fun x => by simpa [pow_two] using x.isLt
  -- Pointwise bounds.
  have hcolpt : ∀ ij : GroupIndex k × GroupIndex k, Nat.dist (vcol n k ij) (vcol n k ij.swap) ≤
      Nat.dist (groupCol ij.1).val (groupCol ij.2).val*s+k^2 := by
    rintro ⟨i, j⟩
    simp only [vcol, Prod.swap, ← hsdef]
    have t := Nat.dist.triangle_inequality ((groupCol i).val*s+j.val)
      ((groupCol j).val*s+j.val) ((groupCol j).val*s+i.val)
    rw [Nat.dist_add_add_right, Nat.dist_mul_right] at t
    have h2 : Nat.dist ((groupCol j).val*s+j.val) ((groupCol j).val*s+i.val) < k^2 := by
      have := hidx i; have := hidx j; simp only [Nat.dist]; omega
    omega
  have hrowpt : ∀ ij : GroupIndex k × GroupIndex k, Nat.dist (vrow n k ij) (vrow n k ij.swap) =
      Nat.dist (groupRow ij.1).val (groupRow ij.2).val*s := by
    rintro ⟨i, j⟩
    simp only [vrow, Prod.swap, ← hsdef, Nat.dist_add_add_right, Nat.dist_mul_right]
  -- Sums of distances.
  have hC := sum_groupCol_dist k
  have hR := sum_groupRow_dist k
  have hk3' : k^2*(k^3-k) ≤ k^5 := by
    calc k^2*(k^3-k) ≤ k^2*k^3 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = k^5 := by ring
  set DC := ∑ i : GroupIndex k, ∑ j : GroupIndex k, Nat.dist (groupCol i).val (groupCol j).val
  set DR := ∑ i : GroupIndex k, ∑ j : GroupIndex k, Nat.dist (groupRow i).val (groupRow j).val
  have hcard : Fintype.card (GroupIndex k × GroupIndex k) = k^4 := by
    simp [Fintype.card_prod]; ring
  have hchain : ∑ ij ∈ Finset.univ.filter (fun ij : GroupIndex k × GroupIndex k => ij.swap ≠ ij),
        vcost n k ij ≤ k^4*(4*n+3*m+1)+(s*DC+k^4*k^2)*(6*m+5)+s*DR*(2*m+3) := calc
    ∑ ij ∈ Finset.univ.filter (fun ij : GroupIndex k × GroupIndex k => ij.swap ≠ ij),
        vcost n k ij
      ≤ ∑ ij : GroupIndex k × GroupIndex k, vcost n k ij :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ ∑ ij : GroupIndex k × GroupIndex k,
          ((4*n+3*m+1)+(Nat.dist (groupCol ij.1).val (groupCol ij.2).val*s+k^2)*(6*m+5)+
            Nat.dist (groupRow ij.1).val (groupRow ij.2).val*s*(2*m+3)) := by
        apply Finset.sum_le_sum
        intro ij _
        simp only [vcost, ← hsdef, ← hm, hrowpt]
        have := Nat.mul_le_mul_right (6*m+5) (hcolpt ij)
        omega
    _ = k^4*(4*n+3*m+1)+(s*DC+k^4*k^2)*(6*m+5)+s*DR*(2*m+3) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          hcard, smul_eq_mul, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib,
          ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
        simp only [Fintype.sum_prod_type, DC, DR, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hfinal : 3*(k^4*(4*n+3*m+1)+(s*DC+k^4*k^2)*(6*m+5)+s*DR*(2*m+3)) ≤
      8*(k^5*s^2)+66*(k*s^3) := by
        have hn : n = k*s := hk.mul_side.symm
        -- Monomials below `k*s³`, using `s ≥ k³`.
        have hs1 : 1 ≤ s := by nlinarith
        have hk6 : k^6 ≤ s^2 := by nlinarith [Nat.mul_le_mul hks hks]
        have hk5 : k^5 ≤ s^2 := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hk6
        have hk4 : k^4 ≤ s^2 := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hk6
        have e1 : k^5*s ≤ k*s^3 := by
          calc k^5*s = k*s*k^4 := by ring
            _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk4
            _ = k*s^3 := by ring
        have e2 : k^6*s ≤ k*s^3 := by
          calc k^6*s = k*s*k^5 := by ring
            _ ≤ k*s*s^2 := Nat.mul_le_mul_left _ hk5
            _ = k*s^3 := by ring
        have e3 : k^6 ≤ k*s^3 := by
          calc k^6 = k*k^5 := by ring
            _ ≤ k*(s^2*s) := Nat.mul_le_mul_left _ (le_trans hk5 (Nat.le_mul_of_pos_right _ hs1))
            _ = k*s^3 := by ring
        have e4 : k^4*s ≤ k*s^3 := le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right
          (by omega) (by omega : 4 ≤ 5))) e1
        have e5 : k^4 ≤ k*s^3 := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) e3
        have hDC : 3*DC ≤ k^5 := hC ▸ hk3'
        have hDR : 3*DR ≤ k^5 := hR ▸ hk3'
        have hA : 3*((s*DC+k^4*k^2)*(6*m+5)) ≤ (s*k^5+3*k^6)*(6*s+5) := by
          have h1 : 3*(s*DC+k^4*k^2) ≤ s*k^5+3*k^6 := by
            have := Nat.mul_le_mul_left s hDC
            have e : k^4*k^2 = k^6 := by ring
            rw [e]; nlinarith
          calc 3*((s*DC+k^4*k^2)*(6*m+5)) = (3*(s*DC+k^4*k^2))*(6*m+5) := by ring
            _ ≤ (s*k^5+3*k^6)*(6*s+5) := Nat.mul_le_mul h1 (by omega)
        have hB : 3*(s*DR*(2*m+3)) ≤ s*k^5*(2*s+3) := by
          calc 3*(s*DR*(2*m+3)) = s*(3*DR)*(2*m+3) := by ring
            _ ≤ s*k^5*(2*s+3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hDR) (by omega)
        have hT : 3*(k^4*(4*n+3*m+1)) ≤ 12*(k^5*s)+9*(k^4*s)+3*k^4 := by
          rw [hn]
          have := Nat.mul_le_mul_left (k^4) (show 4*(k*s)+3*m+1 ≤ 4*(k*s)+3*s+1 by omega)
          nlinarith
        have hexpA : (s*k^5+3*k^6)*(6*s+5) = 6*(k^5*s^2)+5*(k^5*s)+18*(k^6*s)+15*k^6 := by ring
        have hexpB : s*k^5*(2*s+3) = 2*(k^5*s^2)+3*(k^5*s) := by ring
        omega
  omega

end SlidingPuzzle.Partition
