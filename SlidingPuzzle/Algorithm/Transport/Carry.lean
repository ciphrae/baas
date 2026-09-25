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

/-- Exit through a tile carry. The selected source tile lies at least two
columns into its reservoir. -/
theorem exists_transport_carry_exit [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j i (blank S))
    (hrow : (blank S).1 = b.1)
    (hx : (groupCol j).val*side n k+k^2+2 ≤ b.2.val) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells S (blank S) b) ∧
      p.length ≤ 6*side n k+69*k^2+176 := by
  have hn2 : 2 ≤ n := by have := hk.two_le_n; omega
  obtain ⟨-, hk2, -, -, -⟩ := hk.facts
  have hk3 : k^2+4 ≤ side n k := by have := hk.sq_add_le; have := hk.two_le; omega
  have hiLt : i.val < k^2 := by simp [pow_two]
  have hrowEnd : ((groupRow j).val+1)*side n k ≤ n := by
    calc
      _ ≤ k*side n k := Nat.mul_le_mul_right _ (groupRow j).isLt
      _ = n := hk.mul_side
  have hcolEnd : ((groupCol j).val+1)*side n k ≤ n := by
    calc
      _ ≤ k*side n k := Nat.mul_le_mul_right _ (groupCol j).isLt
      _ = n := hk.mul_side
  simp only [Nat.add_mul, Nat.one_mul] at hrowEnd hcolEnd
  obtain ⟨hv1, hv2, hv3⟩ := hblank
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  simp only [Nat.add_mul, Nat.one_mul] at hv2 hb2 hb4
  have hsb : S b ∈ targetGroup i := by
    apply hAS.mem_targetGroup ht
    intro h
    rw [h] at hb3
    omega
  set c := blank S with hcdef
  let R := b.1
  let L := (groupCol j).val*side n k+k^2
  let δ := if (c.2.val+L) % 2 = 1 then 0 else 1
  have hδ : δ ≤ 1 := by dsimp [δ]; split_ifs <;> omega
  have hpar : (c.2.val+(L+δ)) % 2 = 1 := by dsimp [δ]; split_ifs <;> omega
  let w := L+δ
  have hw : w+1 ≤ b.2.val := by dsimp [w, L]; omega
  let Hv : ℕ := if R.val+1 < (groupRow j).val*side n k+side n k then R.val+1 else R.val-1
  have hHv : (groupRow j).val*side n k+k ≤ Hv ∧ Hv < (groupRow j).val*side n k+side n k ∧
      Nat.dist R.val Hv = 1 := by
    have hkk : k+2 ≤ side n k := by nlinarith
    have := hb1; have := hb2
    dsimp [Hv, R]; split_ifs <;> simp only [Nat.dist] <;> omega
  let H : Fin n := ⟨Hv, by have := hHv.2.1; omega⟩
  let e : Cell n := (R, ⟨w, by omega⟩)
  let z : Cell n := (R, ⟨w+1, by omega⟩)
  let c' : Cell n := (H, c.2)
  have hres : ∀ x : Cell n, (x.1 = R ∨ x.1 = H) → w ≤ x.2.val → x.2.val ≤ b.2.val →
      reservoir j x := by
    intro x hx hlo hhi
    have hrow' : (groupRow j).val*side n k+k ≤ x.1.val ∧ x.1.val < (groupRow j).val*side n k+side n k := by
      rcases hx with hx | hx <;> rw [hx]
      · exact ⟨hb1, hb2⟩
      · exact ⟨hHv.1, hHv.2.1⟩
    refine ⟨hrow'.1, by simp only [Nat.add_mul, Nat.one_mul]; exact hrow'.2,
      by dsimp [w, L] at hlo; omega, by simp only [Nat.add_mul, Nat.one_mul]; omega⟩
  have hcout : ∀ r : GroupIndex k, ¬ reservoir r c :=
    fun r hr => vertical_not_reservoir hk (⟨hv1, by simp only [Nat.add_mul, Nat.one_mul]; exact hv2, hv3⟩ : vertical j i c) hr
  have hvc' : vertical j i c' := ⟨hHv.1, by simp only [Nat.add_mul, Nat.one_mul]; exact hHv.2.1, hv3⟩
  have hc'out : ∀ r : GroupIndex k, ¬ reservoir r c' := fun r hr => vertical_not_reservoir hk hvc' hr
  have he : reservoir j e := hres e (Or.inl rfl) le_rfl (by dsimp [e]; omega)
  have hz : reservoir j z := hres z (Or.inl rfl) (by dsimp [z]; omega) (by dsimp [z]; omega)
  have hcR : c.1 = R := hrow
  have hcc' : c ≠ c' := by
    intro h
    have := congrArg (fun x : Cell n => x.1.val) h
    simp only [c', H] at this
    rw [hcR] at this
    have := hHv.2.2
    simp only [Nat.dist] at this
    omega
  -- E1: short jump into the reservoir.
  obtain ⟨p₁, hp₁⟩ := exists_horizontal_jump hn2 S e
    (by rw [← hcdef, hcR]; simp [Nat.dist, e])
    (by rw [← hcdef, hcR]; dsimp [e]; omega)
  let S₁ := swapCells S c e
  have hbS₁ : blank S₁ = e := blank_swapCells S e
  -- E2: walk to the tile and carry it to column w+1.
  obtain ⟨S₁', cs₁, hE₁, hl₁, hbS₁', hin₁⟩ :=
    exists_row_walk S₁ R w (b.2.val-1-w) (by omega) (by rw [hbS₁])
  obtain ⟨S₂, cs₂, hE₂, hl₂, hbS₂, htile, hin₂⟩ :=
    exists_carry S₁' R H hHv.2.2 w (b.2.val-1-w) (by omega) (by rw [hbS₁'])
  have hE := hE₁.append hE₂
  have hin : ∀ x ∈ cs₁ ++ cs₂, reservoir j x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hin₁ x hx
      exact hres x (Or.inl this.1) (by omega) (by omega)
    · have := hin₂ x hx
      exact hres x this.1 this.2.1 (by omega)
  have hmat₂ : boardMatrix hk S₂ = boardMatrix hk S₁ :=
    hE.boardMatrix_eq_of_reservoir hk (by rw [hbS₁]; exact he) hin
  have hout₂ : ∀ x, ¬ reservoir j x → S₂ x = S₁ x :=
    fun x hx => hE.eq_of_not_reservoir (by rw [hbS₁]; exact he) hin hx
  have hbS₂' : blank S₂ = e := by rw [hbS₂]
  have hS₂z : S₂ z = S b := by
    have hzb : (R, ⟨w+(b.2.val-1-w)+1, by omega⟩) = b := by
      ext <;> simp [R]; omega
    have h1 : S₂ z = S₁' b := by rw [← hzb]; exact htile
    rw [h1]
    have hbw : b ∉ cs₁ := by
      intro hm
      have := hin₁ b hm
      omega
    have hbe : b ≠ blank S₁ := by
      rw [hbS₁]; intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e] at this; omega
    rw [hE₁.preserves hbe hbw]
    apply swapCells_preserves
    · intro h; rw [h] at hb3; omega
    · intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e] at this; omega
  -- E3: jump the blank back to the corridor cell.
  obtain ⟨p₃, hp₃⟩ := exists_horizontal_jump hn2 S₂ c
    (by rw [hbS₂', hcR]; simp [Nat.dist, e])
    (by rw [hbS₂', hcR]; dsimp [e]; omega)
  let S₃ := swapCells S₂ (blank S₂) c
  have hbS₃ : blank S₃ = c := blank_swapCells S₂ c
  -- E4: one corridor move.
  have hd₄ : gridDistance (blank S₃) c' = 1 := by
    rw [hbS₃]
    have := hHv.2.2
    simp only [gridDistance, c', H, Nat.dist] at this ⊢
    rw [hcR]
    omega
  let S₄ := swapCells S₃ (blank S₃) c'
  have hbS₄ : blank S₄ = c' := blank_swapCells S₃ c'
  -- E5: jump the carried tile into the corridor.
  obtain ⟨p₅, hp₅⟩ := exists_horizontal_jump hn2 S₄ z
    (by rw [hbS₄]; have := hHv.2.2; simp only [Nat.dist] at this ⊢; dsimp [c', z, H]; omega)
    (by rw [hbS₄]; have := hHv.2.2; simp only [Nat.dist] at this; dsimp [c', z, H, w] at hpar ⊢; omega)
  let D := swapCells S₄ (blank S₄) z
  obtain ⟨q, hq⟩ := hE.exists_path
  have hbD : blank D = z := blank_swapCells S₄ z
  have hce : c ≠ e := fun h => hcout j (h ▸ he)
  have hc'e : c' ≠ e := fun h => hc'out j (h ▸ he)
  have hcz : c ≠ z := fun h => hcout j (h ▸ hz)
  have hc'z : c' ≠ z := fun h => hc'out j (h ▸ hz)
  have hez : e ≠ z := by
    intro h; have := congrArg (fun x : Cell n => x.2.val) h; simp [e, z] at this
  -- Pointwise effect outside the reservoir.
  have hS₁ : ∀ x, x ≠ c → x ≠ e → S₁ x = S x := fun x h₁ h₂ => swapCells_preserves S h₁ h₂
  have hS₃ : ∀ x, x ≠ e → x ≠ c → S₃ x = S₂ x := fun x h₁ h₂ => by
    change swapCells S₂ (blank S₂) c x = _
    exact swapCells_preserves S₂ (by rw [hbS₂']; exact h₁) h₂
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
    hAS.mem_targetGroup (hA.2 j i c' hvc') (fun h => hcc' (by rw [hcdef]; exact h.symm))
  have hvc : vertical j i c :=
    ⟨hv1, by simp only [Nat.add_mul, Nat.one_mul]; exact hv2, hv3⟩
  refine ⟨D, p₁.append (q.append (p₃.append ((movePath S₃ c' hd₄).append p₅))), ?_, ?_, ?_, ?_⟩
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
    have hS₂e0 : S₂ e ∉ targetGroup g' := by rw [← hbS₂']; exact tile_blank_not_mem_targetGroup S₂ g'
    have hS₄c'0 : S₄ c' ∉ targetGroup g' := by
      rw [← hbS₄]; exact tile_blank_not_mem_targetGroup S₄ g'
    have hbres : reservoir j b := ⟨hb1, by simp only [Nat.add_mul, Nat.one_mul]; exact hb2,
      hb3, by simp only [Nat.add_mul, Nat.one_mul]; exact hb4⟩
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
        show swapCells S₂ (blank S₂) c = _; rw [hbS₂']
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
      have := reservoirCount_swap_out hk S hbres hcout r' g'
      rw [if_neg (show ¬ (r' = j ∧ S c ∈ targetGroup g') from fun h => hSc0 h.2),
        swapCells_comm] at this
      exact this
    omega
  · have hd₁ : Nat.dist c.2.val w ≤ k^2+1 := by
      simp only [Nat.dist]; dsimp [w, L]; omega
    have hd₅ : Nat.dist c.2.val (w+1) ≤ k^2+2 := by
      simp only [Nat.dist]; dsimp [w, L]; omega
    have hp₁' : p₁.length ≤ 25*(k^2+2) := by
      refine hp₁.trans ?_
      have : Nat.dist (blank S).2.val e.2.val ≤ k^2+1 := by rw [← hcdef]; exact hd₁
      omega
    have hp₃' : p₃.length ≤ 25*(k^2+2) := by
      refine hp₃.trans ?_
      have : Nat.dist (blank S₂).2.val c.2.val ≤ k^2+1 := by
        rw [hbS₂', Nat.dist_comm]; exact hd₁
      omega
    have hp₅' : p₅.length ≤ 25*(k^2+3) := by
      refine hp₅.trans ?_
      have : Nat.dist (blank S₄).2.val z.2.val ≤ k^2+2 := by rw [hbS₄]; exact hd₅
      omega
    have hqlen : q.length ≤ 6*(side n k-k^2-2) := by
      rw [hq, List.length_append, hl₁, hl₂]
      dsimp [w, L]; omega
    have hk23 : k^2 ≤ side n k := by omega
    refine (le_of_eq (Path.length_append₅ _ _ _ _ _)).trans ?_
    rw [movePath_length]
    generalize p₁.length = a₁ at hp₁' ⊢
    generalize q.length = a₂ at hqlen ⊢
    generalize p₃.length = a₃ at hp₃' ⊢
    generalize p₅.length = a₅ at hp₅' ⊢
    clear * - hp₁' hqlen hp₃' hp₅' hk23 hk3
    omega

/-- The exit used by Transport: carry the tile when it lies deep in its
reservoir, and jump directly when it is already next to the corridors. -/
theorem exists_transport_exit_count [NeZero n] (hk : Dims n k)
    (A S : Board n) (hA : Clear (k := k) A) (i j : GroupIndex k)
    (hAS : GroupEquivalent i A S) (b : Cell n) (hb : reservoir j b)
    (ht : A b ∈ targetGroup i) (hblank : vertical j i (blank S))
    (hrow : (blank S).1 = b.1) :
    ∃ D : Board n, ∃ p : Path S D, Clear (k := k) D ∧ reservoir j (blank D) ∧
      boardMatrix hk D = boardMatrix hk (swapCells A (blank A) b) ∧
      p.inefficientMoves ≤ 6*side n k+69*k^2+176 := by
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
      exists_transport_exit_path hk A S hA i j hAS b hb ht hblank hrow
    have hbD : reservoir j (blank D) := by rw [hD]; exact hb
    refine ⟨D, p, hAD.clear hk hA hbD, hbD, hAD.boardMatrix_eq_swap hk i A D b ht hD, ?_⟩
    have hiLt : i.val < k^2 := by simp [pow_two]
    have hcol := hblank.2.2
    have hb3 := hb.2.2.1
    have hdist : Nat.dist (blank S).2.val b.2.val ≤ k^2+1 := by
      simp only [Nat.dist]; omega
    omega

end
end SlidingPuzzle.Partition
