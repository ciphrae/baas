import SlidingPuzzle.Moves.Carry
import SlidingPuzzle.Algorithm.Transport.ReservoirSlide
import SlidingPuzzle.Algorithm.Transport.Exit

/-! The exit from a vertical corridor into the source reservoir. Instead of one
long restoring jump to the selected tile (cost `25` per cell), the blank enters
the reservoir by a short jump, walks to the tile, and carries it to the
reservoir's corridor side (cost `6` per cell). Three short jumps then exchange it into the corridor. Only the
reservoir's counts are tracked; its cells may be permuted. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

variable {n k : ℕ}

theorem tile_blank_not_mem_targetGroup [NeZero n] (X : Board n) (g : GroupIndex k) :
    X (blank X) ∉ targetGroup g := by
  simp [blank, position]

/-- Exchanging a reservoir cell with a non-reservoir cell moves one label
into or out of that reservoir. -/
theorem reservoirCount_swap_out (hk : Dims n k) (X : Board n) {y c : Cell n}
    {J : GroupIndex k} (hy : reservoir J y) (hc : ∀ r : GroupIndex k, ¬ reservoir r c)
    (r g : GroupIndex k) :
    reservoirCount (swapCells X y c) r g + (if r = J ∧ X y ∈ targetGroup g then 1 else 0) =
      reservoirCount X r g + (if r = J ∧ X c ∈ targetGroup g then 1 else 0) := by
  have hyc : y ≠ c := fun h => hc J (h ▸ hy)
  have h := reservoirCount_swap_balance X y c hyc r g
  have hiff : reservoir r y ↔ r = J := ⟨fun h => reservoir_unique hk h hy, fun h => h ▸ hy⟩
  simp only [hiff, hc r, false_and, ↓reduceIte, add_zero] at h
  omega

/-- Exchanging two non-reservoir cells does not change any count. -/
theorem reservoirCount_swap_outside (X : Board n) {a c : Cell n}
    (ha : ∀ r : GroupIndex k, ¬ reservoir r a) (hc : ∀ r : GroupIndex k, ¬ reservoir r c)
    (hac : a ≠ c) (r g : GroupIndex k) :
    reservoirCount (swapCells X a c) r g = reservoirCount X r g := by
  have h := reservoirCount_swap_balance X a c hac r g
  simp only [ha r, hc r, false_and, ↓reduceIte, add_zero] at h
  exact h

/-- Walks confined to one reservoir preserve every count. -/
theorem _root_.SlidingPuzzle.Executes.boardMatrix_eq_of_reservoir [NeZero n] (hk : Dims n k)
    {B C : Board n} {cs : List (Cell n)} (h : Executes B cs C) {J : GroupIndex k}
    (hb : reservoir J (blank B)) (hcs : ∀ x ∈ cs, reservoir J x) :
    boardMatrix hk C = boardMatrix hk B := by
  induction h with
  | nil => rfl
  | @cons B C c cs adj rest ih =>
    have hc : reservoir J c := hcs c (by simp)
    rw [ih (by rw [blank_swapCells]; exact hc) (fun x hx => hcs x (by simp [hx]))]
    apply boardMatrix_swap_same_reservoir hk B hb hc
    intro h
    rw [h] at adj
    simp at adj

theorem _root_.SlidingPuzzle.Executes.eq_of_not_reservoir [NeZero n] {B C : Board n} {cs : List (Cell n)}
    (h : Executes B cs C) {J : GroupIndex k}
    (hb : reservoir J (blank B)) (hcs : ∀ x ∈ cs, reservoir J x)
    {x : Cell n} (hx : ¬ reservoir J x) : C x = B x :=
  h.preserves (fun h => hx (h ▸ hb)) (fun h => hx (hcs x h))

theorem _root_.SlidingPuzzle.Path.length_append₅ [NeZero n] {X Y Z W V U : Board n}
    (a : Path X Y) (b : Path Y Z) (c : Path Z W) (d : Path W V) (e : Path V U) :
    (a.append (b.append (c.append (d.append e)))).length =
      a.length + (b.length + (c.length + (d.length + e.length))) := by
  simp only [Path.length_append]

/-- The orientation-free core of a carry exit. The blank starts in a vertical
corridor cell of group `i`, jumps into the source reservoir at `e`, moves the
source tile to `z` inside the reservoir (`hwalk`), jumps back, steps to the
neighboring corridor cell `c'`, and jumps the tile into it. -/
theorem exists_transport_exit_core [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j jc : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hvc : vertical jc i (blank S))
    (c' : Cell n) (hvc' : vertical jc i c') (hd₄ : gridDistance (blank S) c' = 1)
    (e z : Cell n) (he : reservoir j e) (hz : reservoir j z) (hez : e ≠ z) (hbe : b ≠ e)
    (hrowe : Nat.dist (blank S).1.val e.1.val ≤ 1)
    (hpare : ((blank S).1.val+(blank S).2.val+e.1.val+e.2.val) % 2 = 1)
    (hrowz : Nat.dist c'.1.val z.1.val ≤ 1)
    (hparz : (c'.1.val+c'.2.val+z.1.val+z.2.val) % 2 = 1) (L : ℕ)
    (hwalk : ∀ X : Board n, blank X = e → ∃ Y cs, Executes X cs Y ∧ cs.length ≤ L ∧
      blank Y = e ∧ Y z = X b ∧ ∀ x ∈ cs, reservoir j x) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells S (blank S) b) ∧
      p.length ≤ 50*(Nat.dist (blank S).2.val e.2.val+1)+L+1+
        25*(Nat.dist c'.2.val z.2.val+1) := by
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  set c := blank S with hcdef
  have hcout : ∀ r : GroupIndex k, ¬ reservoir r c := fun r hr => vertical_not_reservoir hk hvc hr
  have hc'out : ∀ r : GroupIndex k, ¬ reservoir r c' :=
    fun r hr => vertical_not_reservoir hk hvc' hr
  have hbc : b ≠ c := fun h => hcout j (h ▸ hb)
  have hsb : S b ∈ targetGroup i := hAS.mem_targetGroup ht hbc
  have hcc' : c ≠ c' := by
    intro h; rw [← h, gridDistance_self] at hd₄; omega
  -- E1: short jump into the reservoir.
  obtain ⟨p₁, hp₁⟩ := exists_horizontal_jump hn2 S e hrowe hpare
  let S₁ := swapCells S c e
  have hbS₁ : blank S₁ = e := blank_swapCells S e
  -- E2: move the tile to `z` inside the reservoir.
  obtain ⟨S₂, cs, hE, hl, hbS₂, hS₂z', hin⟩ := hwalk S₁ hbS₁
  have hmat₂ : boardMatrix hk S₂ = boardMatrix hk S₁ :=
    hE.boardMatrix_eq_of_reservoir hk (by rw [hbS₁]; exact he) hin
  have hout₂ : ∀ x, ¬ reservoir j x → S₂ x = S₁ x :=
    fun x hx => hE.eq_of_not_reservoir (by rw [hbS₁]; exact he) hin hx
  have hS₂z : S₂ z = S b := by
    rw [hS₂z']; exact swapCells_preserves S hbc hbe
  -- E3: jump the blank back to the corridor cell.
  obtain ⟨p₃, hp₃⟩ := exists_horizontal_jump hn2 S₂ c
    (by rw [hbS₂, Nat.dist_comm]; exact hrowe) (by rw [hbS₂]; omega)
  let S₃ := swapCells S₂ (blank S₂) c
  have hbS₃ : blank S₃ = c := blank_swapCells S₂ c
  -- E4: one corridor move.
  have hd₄' : gridDistance (blank S₃) c' = 1 := by rw [hbS₃]; exact hd₄
  let S₄ := swapCells S₃ (blank S₃) c'
  have hbS₄ : blank S₄ = c' := blank_swapCells S₃ c'
  -- E5: jump the carried tile into the corridor.
  obtain ⟨p₅, hp₅⟩ := exists_horizontal_jump hn2 S₄ z
    (by rw [hbS₄]; exact hrowz) (by rw [hbS₄]; exact hparz)
  let D := swapCells S₄ (blank S₄) z
  obtain ⟨q, hq⟩ := hE.exists_path
  have hbD : blank D = z := blank_swapCells S₄ z
  have hce : c ≠ e := fun h => hcout j (h ▸ he)
  have hc'e : c' ≠ e := fun h => hc'out j (h ▸ he)
  have hcz : c ≠ z := fun h => hcout j (h ▸ hz)
  have hc'z : c' ≠ z := fun h => hc'out j (h ▸ hz)
  -- Pointwise effect outside the reservoir.
  have hS₁ : ∀ x, x ≠ c → x ≠ e → S₁ x = S x := fun x h₁ h₂ => swapCells_preserves S h₁ h₂
  have hS₃ : ∀ x, x ≠ e → x ≠ c → S₃ x = S₂ x := fun x h₁ h₂ => by
    change swapCells S₂ (blank S₂) c x = _
    exact swapCells_preserves S₂ (by rw [hbS₂]; exact h₁) h₂
  have hS₄ : ∀ x, x ≠ c → x ≠ c' → S₄ x = S₃ x := fun x h₁ h₂ => by
    change swapCells S₃ (blank S₃) c' x = _
    exact swapCells_preserves S₃ (by rw [hbS₃]; exact h₁) h₂
  have hDx : ∀ x, x ≠ c' → x ≠ z → D x = S₄ x := fun x h₁ h₂ => by
    change swapCells S₄ (blank S₄) z x = _
    exact swapCells_preserves S₄ (by rw [hbS₄]; exact h₁) h₂
  have hDS : ∀ x, ¬ reservoir j x → x ≠ c → x ≠ c' → D x = S x := by
    intro x hx h₁ h₂
    have hxe : x ≠ e := fun h => hx (h ▸ he)
    have hxz : x ≠ z := fun h => hx (h ▸ hz)
    rw [hDx x h₂ hxz, hS₄ x h₁ h₂, hS₃ x hxe h₁, hout₂ x hx, hS₁ x h₁ hxe]
  have hS₂c : S₂ c = S e := by
    rw [hout₂ c (hcout j)]
    change swapCells S c e c = _
    exact swapCells_at_left S c e
  have hDc : D c = S c' := by
    rw [hDx c hcc' hcz]
    change swapCells S₃ (blank S₃) c' c = _
    rw [← hbS₃, swapCells_at_left, hS₃ c' hc'e hcc'.symm, hout₂ c' (hc'out j),
      hS₁ c' hcc'.symm hc'e]
  have hS₄z : S₄ z = S b := by
    rw [hS₄ z hcz.symm hc'z.symm, hS₃ z hez.symm hcz.symm, hS₂z]
  have hDc' : D c' = S b := by
    change swapCells S₄ (blank S₄) z c' = _
    rw [← hbS₄, swapCells_at_left, hS₄z]
  have hSc' : S c' ∈ targetGroup i :=
    hAS.mem_targetGroup (hA.2 jc i c' hvc') (fun h => hcc' (by rw [hcdef]; exact h.symm))
  refine ⟨D, p₁.append (q.append (p₃.append ((movePath S₃ c' hd₄').append p₅))), ?_, ?_, ?_, ?_⟩
  · constructor
    · intro l x hx
      have hxc : x ≠ c := fun h => horizontal_not_vertical hk hx (h ▸ hvc)
      have hxc' : x ≠ c' := fun h => horizontal_not_vertical hk hx (h ▸ hvc')
      rw [hDS x (fun h => horizontal_not_reservoir hk hx h) hxc hxc']
      exact ((hAS x l).mp (Or.inl (hA.1 l x hx))).resolve_right
        (fun h => hxc (h.1.trans hcdef.symm))
    · intro l m x hx
      by_cases hxc : x = c
      · subst hxc
        obtain ⟨rfl, rfl⟩ := vertical_unique hk hx hvc
        rw [hDc]; exact hSc'
      by_cases hxc' : x = c'
      · subst hxc'
        obtain ⟨rfl, rfl⟩ := vertical_unique hk hx hvc'
        rw [hDc']; exact hsb
      rw [hDS x (fun h => vertical_not_reservoir hk hx h) hxc hxc']
      exact ((hAS x m).mp (Or.inl (hA.2 l m x hx))).resolve_right
        (fun h => hxc (h.1.trans hcdef.symm))
  · rw [hbD]; exact hz
  · funext r g
    have h₂ := congrFun (congrFun hmat₂ r) g
    unfold boardMatrix at h₂ ⊢
    generalize transportIndex k hk r = r' at h₂ ⊢
    generalize transportIndex k hk g = g' at h₂ ⊢
    have hSc0 : S c ∉ targetGroup g' := by rw [hcdef]; exact tile_blank_not_mem_targetGroup S g'
    have hS₂e0 : S₂ e ∉ targetGroup g' := by
      rw [← hbS₂]; exact tile_blank_not_mem_targetGroup S₂ g'
    have hS₄c'0 : S₄ c' ∉ targetGroup g' := by
      rw [← hbS₄]; exact tile_blank_not_mem_targetGroup S₄ g'
    have h₁ : reservoirCount S₁ r' g' + (if r' = j ∧ S e ∈ targetGroup g' then 1 else 0) =
        reservoirCount S r' g' := by
      have := reservoirCount_swap_out hk S he hcout r' g'
      rw [if_neg (show ¬ (r' = j ∧ S c ∈ targetGroup g') from fun h => hSc0 h.2),
        swapCells_comm] at this
      exact this
    have h₃ : reservoirCount S₃ r' g' =
        reservoirCount S₂ r' g' + (if r' = j ∧ S e ∈ targetGroup g' then 1 else 0) := by
      have := reservoirCount_swap_out hk S₂ he hcout r' g'
      rw [if_neg (show ¬ (r' = j ∧ S₂ e ∈ targetGroup g') from fun h => hS₂e0 h.2),
        hS₂c] at this
      have hdef : S₃ = swapCells S₂ e c := by
        show swapCells S₂ (blank S₂) c = _; rw [hbS₂]
      rw [hdef]; omega
    have h₄ : reservoirCount S₄ r' g' = reservoirCount S₃ r' g' := by
      have hdef : S₄ = swapCells S₃ c c' := by
        show swapCells S₃ (blank S₃) c' = _; rw [hbS₃]
      rw [hdef]
      exact reservoirCount_swap_outside S₃ hcout hc'out hcc' r' g'
    have h₅ : reservoirCount D r' g' + (if r' = j ∧ S b ∈ targetGroup g' then 1 else 0) =
        reservoirCount S₄ r' g' := by
      have := reservoirCount_swap_out hk S₄ hz hc'out r' g'
      rw [if_neg (show ¬ (r' = j ∧ S₄ c' ∈ targetGroup g') from fun h => hS₄c'0 h.2),
        hS₄z] at this
      have hdef : D = swapCells S₄ z c' := by
        show swapCells S₄ (blank S₄) z = _; rw [hbS₄, swapCells_comm]
      rw [hdef]; exact this
    have h₆ : reservoirCount (swapCells S c b) r' g' +
        (if r' = j ∧ S b ∈ targetGroup g' then 1 else 0) = reservoirCount S r' g' := by
      have := reservoirCount_swap_out hk S hb hcout r' g'
      rw [if_neg (show ¬ (r' = j ∧ S c ∈ targetGroup g') from fun h => hSc0 h.2),
        swapCells_comm] at this
      exact this
    omega
  · have hp₃' : p₃.length ≤ 25*(Nat.dist c.2.val e.2.val+1) := by
      refine hp₃.trans ?_
      rw [hbS₂, Nat.dist_comm]
    have hqlen : q.length ≤ L := by rw [hq]; exact hl
    refine (le_of_eq (Path.length_append₅ _ _ _ _ _)).trans ?_
    rw [movePath_length]
    have hcol₅ : (blank S₄).2 = c'.2 := by rw [hbS₄]
    rw [hcol₅] at hp₅
    have hcol₁ : (blank S).2 = c.2 := by rw [hcdef]
    rw [hcol₁] at hp₁
    generalize p₁.length = a₁ at hp₁ ⊢
    generalize q.length = a₂ at hqlen ⊢
    generalize p₃.length = a₃ at hp₃' ⊢
    generalize p₅.length = a₅ at hp₅ ⊢
    omega

/-- A helper row next to a reservoir row, inside the same row band. -/
theorem exists_helper_row (hk : Dims n k) (j : GroupIndex k) (R : Fin n)
    (hR : (groupRow j).val*side n k+k ≤ R.val ∧ R.val < (groupRow j).val*side n k+side n k) :
    ∃ H : Fin n, (groupRow j).val*side n k+k ≤ H.val ∧
      H.val < (groupRow j).val*side n k+side n k ∧ Nat.dist R.val H.val = 1 := by
  have hkk : k+2 ≤ side n k := hk.k_add_two_le
  have hblock := hk.block_le (groupRow j)
  simp only [Nat.add_mul, Nat.one_mul] at hblock
  by_cases h : R.val+1 < (groupRow j).val*side n k+side n k
  · exact ⟨⟨R.val+1, by omega⟩, by dsimp; omega, h, by simp [Nat.dist]⟩
  · exact ⟨⟨R.val-1, by omega⟩, by dsimp; omega, by dsimp; omega, by simp [Nat.dist]; omega⟩

/-- Exit to the left through a tile carry. The selected source tile lies at
least two columns into its reservoir. -/
theorem exists_transport_carry_exit [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j i (blank S))
    (hrow : (blank S).1 = b.1)
    (hx : (groupCol j).val*side n k+k^2+2 ≤ b.2.val) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells S (blank S) b) ∧
      p.length ≤ 6*(b.2.val-(groupCol j).val*side n k)+75*k^2+176 := by
  obtain ⟨-, hk2, -, -, -⟩ := hk.facts
  have hiLt : i.val < k^2 := by simp [pow_two]
  have hcolEnd : ((groupCol j).val+1)*side n k ≤ n := by
    calc
      _ ≤ k*side n k := Nat.mul_le_mul_right _ (groupCol j).isLt
      _ = n := hk.mul_side
  simp only [Nat.add_mul, Nat.one_mul] at hcolEnd
  have hbv := hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbv
  simp only [Nat.add_mul, Nat.one_mul] at hb2 hb4
  have hv3 := hblank.2.2
  set c := blank S with hcdef
  let R := b.1
  obtain ⟨H, hH1, hH2, hRH⟩ := exists_helper_row hk j R ⟨hb1, hb2⟩
  let L := (groupCol j).val*side n k+k^2
  let δ := if (c.2.val+L) % 2 = 1 then 0 else 1
  have hpar : (c.2.val+(L+δ)) % 2 = 1 := by dsimp [δ]; split_ifs <;> omega
  let w := L+δ
  have hw : w+1 ≤ b.2.val := by dsimp [w, L, δ]; split_ifs <;> omega
  let e : Cell n := (R, ⟨w, by omega⟩)
  let z : Cell n := (R, ⟨w+1, by omega⟩)
  let c' : Cell n := (H, c.2)
  have hres : ∀ x : Cell n, (x.1 = R ∨ x.1 = H) → w ≤ x.2.val → x.2.val ≤ b.2.val →
      reservoir j x := by
    intro x hx hlo hhi
    have hrow' : (groupRow j).val*side n k+k ≤ x.1.val ∧
        x.1.val < (groupRow j).val*side n k+side n k := by
      rcases hx with hx | hx <;> rw [hx]
      · exact ⟨hb1, hb2⟩
      · exact ⟨hH1, hH2⟩
    refine ⟨hrow'.1, by simp only [Nat.add_mul, Nat.one_mul]; exact hrow'.2,
      by dsimp [w, L] at hlo; omega, by simp only [Nat.add_mul, Nat.one_mul]; omega⟩
  have hvc' : vertical j i c' := ⟨hH1, by simp only [Nat.add_mul, Nat.one_mul]; exact hH2, hv3⟩
  have hcR : c.1 = R := hrow
  have hd₄ : gridDistance c c' = 1 := by
    simp only [gridDistance, c', Nat.dist] at hRH ⊢
    rw [hcR]; omega
  have he : reservoir j e := hres e (Or.inl rfl) le_rfl (by dsimp [e]; omega)
  have hz : reservoir j z := hres z (Or.inl rfl) (by dsimp [z]; omega) (by dsimp [z]; omega)
  obtain ⟨D, p, hD, hbD, hm, hl⟩ := exists_transport_exit_core hk A S hA i j j hAS b hb ht
    hblank c' hvc' hd₄ e z he hz
    (by intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e, z] at this)
    (by intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e] at this; omega)
    (by rw [← hcdef, hcR]; simp [Nat.dist, e])
    (by rw [← hcdef, hcR]; dsimp [e]; omega)
    (by simp only [Nat.dist] at hRH ⊢; dsimp [c', z]; omega)
    (by simp only [Nat.dist] at hRH; dsimp [c', z, w] at hpar ⊢; omega)
    (6*(b.2.val-1-w)) (by
      intro X hX
      obtain ⟨X₁, cs₁, hE₁, hl₁, hbX₁, hin₁⟩ :=
        exists_row_walk X R w (b.2.val-1-w) (by omega) (by rw [hX])
      obtain ⟨Y, cs₂, hE₂, hl₂, hbY, htile, hin₂⟩ :=
        exists_carry X₁ R H hRH w (b.2.val-1-w) (by omega) (by rw [hbX₁])
      refine ⟨Y, cs₁ ++ cs₂, hE₁.append hE₂, by simp only [List.length_append]; omega,
        by rw [hbY], ?_, ?_⟩
      · have hzb : (R, ⟨w+(b.2.val-1-w)+1, by omega⟩) = b := by
          ext <;> simp [R]; omega
        have h1 : Y z = X₁ b := by rw [← hzb]; exact htile
        rw [h1]
        have hbw : b ∉ cs₁ := by
          intro hm
          have := hin₁ b hm
          omega
        have hbe : b ≠ blank X := by
          rw [hX]; intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e] at this
          omega
        exact hE₁.preserves hbe hbw
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := hin₁ x hx
          exact hres x (Or.inl this.1) (by omega) (by omega)
        · have := hin₂ x hx
          exact hres x this.1 this.2.1 (by omega))
  refine ⟨D, p, hD, hbD, hm, hl.trans ?_⟩
  have hd₁ : Nat.dist c.2.val e.2.val ≤ k^2+1 := by
    simp only [Nat.dist]; dsimp [e, w, L, δ]; split_ifs <;> omega
  have hd₅ : Nat.dist c'.2.val z.2.val ≤ k^2+2 := by
    simp only [Nat.dist]; dsimp [c', z, w, L, δ]; split_ifs <;> omega
  have : w ≥ (groupCol j).val*side n k := by dsimp [w, L]; omega
  have h6 : 6*(b.2.val-1-w) ≤ 6*(b.2.val-(groupCol j).val*side n k) := by omega
  nlinarith

/-- Exit to the right: the blank descends the vertical corridor `V(j',i)` of the
square `j'` right of the source square `j`, and the tile is carried rightwards. -/
theorem exists_transport_carry_exit_right [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j j' : GroupIndex k)
    (hrowj : groupRow j' = groupRow j) (hcolj : (groupCol j').val = (groupCol j).val+1)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j' i (blank S))
    (hrow : (blank S).1 = b.1)
    (hx : b.2.val+3 ≤ ((groupCol j).val+1)*side n k) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells S (blank S) b) ∧
      p.length ≤ 6*(((groupCol j).val+1)*side n k-b.2.val)+75*k^2+176 := by
  obtain ⟨-, hk2, -, -, -⟩ := hk.facts
  have hiLt : i.val < k^2 := by simp [pow_two]
  have hbv := hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbv
  simp only [Nat.add_mul, Nat.one_mul] at hb2 hb4 hx
  have hv3 := hblank.2.2
  rw [hcolj] at hv3
  simp only [Nat.add_mul, Nat.one_mul] at hv3
  set c := blank S with hcdef
  let R := b.1
  obtain ⟨H, hH1, hH2, hRH⟩ := exists_helper_row hk j R ⟨hb1, hb2⟩
  let E := (groupCol j).val*side n k+side n k-1
  let δ := if (c.2.val+E) % 2 = 1 then 0 else 1
  have hpar : (c.2.val+(E-δ)) % 2 = 1 := by dsimp [δ, E]; split_ifs <;> omega
  let w := E-δ
  have hw : b.2.val+1 ≤ w := by dsimp [w, E, δ]; split_ifs <;> omega
  have hwn : w < n := by have := c.2.isLt; dsimp [w, E]; omega
  let e : Cell n := (R, ⟨w, hwn⟩)
  let z : Cell n := (R, ⟨w-1, by omega⟩)
  let c' : Cell n := (H, c.2)
  have hres : ∀ x : Cell n, (x.1 = R ∨ x.1 = H) → b.2.val ≤ x.2.val → x.2.val ≤ w →
      reservoir j x := by
    intro x hx hlo hhi
    have hrow' : (groupRow j).val*side n k+k ≤ x.1.val ∧
        x.1.val < (groupRow j).val*side n k+side n k := by
      rcases hx with hx | hx <;> rw [hx]
      · exact ⟨hb1, hb2⟩
      · exact ⟨hH1, hH2⟩
    refine ⟨hrow'.1, by simp only [Nat.add_mul, Nat.one_mul]; exact hrow'.2,
      by omega, by simp only [Nat.add_mul, Nat.one_mul]; dsimp [w, E] at hhi; omega⟩
  have hvc' : vertical j' i c' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hrowj]; exact hH1
    · rw [hrowj]; simp only [Nat.add_mul, Nat.one_mul]; exact hH2
    · rw [hcolj]; simp only [Nat.add_mul, Nat.one_mul]; exact hv3
  have hcR : c.1 = R := hrow
  have hd₄ : gridDistance c c' = 1 := by
    simp only [gridDistance, c', Nat.dist] at hRH ⊢
    rw [hcR]; omega
  have he : reservoir j e := hres e (Or.inl rfl) (by dsimp [e]; omega) le_rfl
  have hz : reservoir j z := hres z (Or.inl rfl) (by dsimp [z]; omega) (by dsimp [z]; omega)
  obtain ⟨D, p, hD, hbD, hm, hl⟩ := exists_transport_exit_core hk A S hA i j j' hAS b hb ht
    hblank c' hvc' hd₄ e z he hz
    (by intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e, z] at this; omega)
    (by intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e] at this; omega)
    (by rw [← hcdef, hcR]; simp [Nat.dist, e])
    (by rw [← hcdef, hcR]; dsimp [e]; omega)
    (by simp only [Nat.dist] at hRH ⊢; dsimp [c', z]; omega)
    (by simp only [Nat.dist] at hRH; dsimp [c', z]; omega)
    (6*(w-1-b.2.val)) (by
      intro X hX
      obtain ⟨X₁, cs₁, hE₁, hl₁, hbX₁, hin₁⟩ :=
        exists_row_walk_left X R (b.2.val+1) (w-1-b.2.val) (by omega) (by
          rw [hX]; ext <;> simp [e]; omega)
      obtain ⟨Y, cs₂, hE₂, hl₂, hbY, htile, hin₂⟩ :=
        exists_carry_right X₁ R H hRH b.2.val (w-1-b.2.val) (by omega) (by rw [hbX₁])
      refine ⟨Y, cs₁ ++ cs₂, hE₁.append hE₂, by simp only [List.length_append]; omega,
        by rw [hbY]; ext <;> simp [e]; omega, ?_, ?_⟩
      · have hzc : ((R, ⟨b.2.val+(w-1-b.2.val), by omega⟩) : Cell n) = z := by
          ext <;> simp [z]; omega
        have hbb : ((R, ⟨b.2.val, by omega⟩) : Cell n) = b := by ext <;> simp [R]
        rw [← hzc, htile, hbb]
        have hbw : b ∉ cs₁ := by
          intro hm
          have := hin₁ b hm
          omega
        have hbe : b ≠ blank X := by
          rw [hX]; intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e] at this
          omega
        exact hE₁.preserves hbe hbw
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := hin₁ x hx
          exact hres x (Or.inl this.1) (by omega) (by omega)
        · have := hin₂ x hx
          exact hres x this.1 this.2.1 (by omega))
  refine ⟨D, p, hD, hbD, hm, hl.trans ?_⟩
  have hd₁ : Nat.dist c.2.val e.2.val ≤ k^2+1 := by
    simp only [Nat.dist]; dsimp [e, w, E, δ]; split_ifs <;> omega
  have hd₅ : Nat.dist c'.2.val z.2.val ≤ k^2+2 := by
    simp only [Nat.dist]; dsimp [c', z, w, E, δ]; split_ifs <;> omega
  have h6 : 6*(w-1-b.2.val) ≤ 6*((groupCol j).val*side n k+side n k-b.2.val) := by
    dsimp [w, E]; omega
  simp only [Nat.add_mul, Nat.one_mul]
  nlinarith

/-- The exit through the source square's own vertical corridor: carry the tile
when it lies deep in its reservoir, and jump directly when it is already next
to the corridors. The cost grows with the tile's distance from the left edge. -/
theorem exists_transport_exit_left [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j i (blank S))
    (hrow : (blank S).1 = b.1) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
      p.inefficientMoves ≤ 6*(b.2.val-(groupCol j).val*side n k)+75*k^2+176 := by
  have hbS : b ≠ blank S := fun h => vertical_not_reservoir hk hblank (h ▸ hb)
  by_cases hx : (groupCol j).val*side n k+k^2+2 ≤ b.2.val
  · obtain ⟨D, p, hD, hbD, hm, hl⟩ :=
      exists_transport_carry_exit hk A S hA i j hAS b hb ht hblank hrow hx
    refine ⟨D, p, hD, hbD, ?_, p.inefficientMoves_le_length.trans hl⟩
    rw [hm]
    have hsb : S b ∈ targetGroup i := hAS.mem_targetGroup ht hbS
    exact GroupEquivalent.boardMatrix_eq_swap hk i A _ b ht
      (hAS.trans (groupEquivalent_swap hk S i b hsb)) (blank_swapCells S b)
  · obtain ⟨D, p, hD, hAD, hp⟩ :=
      exists_transport_exit_path hk A S hA i j hAS b hb ht rfl hblank hrow
    have hbD : reservoir j (blank D) := by rw [hD]; exact hb
    refine ⟨D, p, hAD.clear hk hA hbD, hbD, hAD.boardMatrix_eq_swap hk i A D b ht hD, ?_⟩
    have hiLt : i.val < k^2 := by simp [pow_two]
    have hcol := hblank.2.2
    have hb3 := hb.2.2.1
    have hdist : Nat.dist (blank S).2.val b.2.val ≤ k^2+1 := by
      simp only [Nat.dist]; omega
    omega

/-- The exit through the vertical corridor of the square `j'` right of the
source square `j`. The cost grows with the tile's distance from the right edge. -/
theorem exists_transport_exit_right [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j j' : GroupIndex k)
    (hrowj : groupRow j' = groupRow j) (hcolj : (groupCol j').val = (groupCol j).val+1)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j' i (blank S))
    (hrow : (blank S).1 = b.1) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
      p.inefficientMoves ≤ 6*(((groupCol j).val+1)*side n k-b.2.val)+75*k^2+176 := by
  have hbS : b ≠ blank S := fun h => vertical_not_reservoir hk hblank (h ▸ hb)
  by_cases hx : b.2.val+3 ≤ ((groupCol j).val+1)*side n k
  · obtain ⟨D, p, hD, hbD, hm, hl⟩ :=
      exists_transport_carry_exit_right hk A S hA i j j' hrowj hcolj hAS b hb ht hblank hrow hx
    refine ⟨D, p, hD, hbD, ?_, p.inefficientMoves_le_length.trans hl⟩
    rw [hm]
    have hsb : S b ∈ targetGroup i := hAS.mem_targetGroup ht hbS
    exact GroupEquivalent.boardMatrix_eq_swap hk i A _ b ht
      (hAS.trans (groupEquivalent_swap hk S i b hsb)) (blank_swapCells S b)
  · obtain ⟨D, p, hD, hAD, hp⟩ :=
      exists_transport_exit_path hk A S hA i j hAS b hb ht hrowj hblank hrow
    have hbD : reservoir j (blank D) := by rw [hD]; exact hb
    refine ⟨D, p, hAD.clear hk hA hbD, hbD, hAD.boardMatrix_eq_swap hk i A D b ht hD, ?_⟩
    have hiLt : i.val < k^2 := by simp [pow_two]
    have hcol := hblank.2.2
    rw [hcolj] at hcol
    have hb4 := hb.2.2.2
    simp only [Nat.add_mul, Nat.one_mul] at hcol hb4 hx
    have hdist : Nat.dist (blank S).2.val b.2.val ≤ k^2+2 := by
      simp only [Nat.dist]; omega
    omega

end
end SlidingPuzzle.Partition
