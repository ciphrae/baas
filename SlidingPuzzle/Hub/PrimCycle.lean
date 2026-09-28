import SlidingPuzzle.Moves.ThreeCycleSharp
import SlidingPuzzle.Moves.ThreeCycleNear
import SlidingPuzzle.Moves.Embedding
import SlidingPuzzle.Moves.Efficiency

/-! # Three-cycles inside a square box

`exists_three_cycle_sharp` on an `m × m` board, lifted by `Path.exists_embedded` into
a square box of the `n × n` board containing the blank. Only the three rotated
cells change; the blank stays where it is. -/
namespace SlidingPuzzle.Hub

variable {n : ℕ} [NeZero n]

/-- The cell lies in the square box with corner `(r0, c0)` and side `m`. -/
def InBox (r0 c0 m : ℕ) (x : Cell n) : Prop :=
  r0 ≤ x.1.val ∧ x.1.val < r0 + m ∧ c0 ≤ x.2.val ∧ x.2.val < c0 + m

omit [NeZero n] in
/-- The embedding of an `m × m` board as the box. -/
def boxEmb (r0 c0 m : ℕ) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) : Cell m ↪ Cell n :=
  ⟨fun x => (⟨r0 + x.1.val, by have := x.1.isLt; omega⟩,
      ⟨c0 + x.2.val, by have := x.2.isLt; omega⟩), by
    intro x y h
    have h₁ := congrArg (fun z : Cell n => z.1.val) h
    have h₂ := congrArg (fun z : Cell n => z.2.val) h
    simp only at h₁ h₂
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))⟩

omit [NeZero n] in
@[simp] theorem boxEmb_fst (r0 c0 m : ℕ) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (x : Cell m) :
    (boxEmb r0 c0 m hr hc x).1.val = r0 + x.1.val := rfl

omit [NeZero n] in
@[simp] theorem boxEmb_snd (r0 c0 m : ℕ) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (x : Cell m) :
    (boxEmb r0 c0 m hr hc x).2.val = c0 + x.2.val := rfl

omit [NeZero n] in
theorem boxEmb_adj (r0 c0 m : ℕ) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (a b : Cell m)
    (h : gridDistance a b = 1) : gridDistance (boxEmb r0 c0 m hr hc a) (boxEmb r0 c0 m hr hc b) = 1 := by
  simp only [gridDistance, Nat.dist, boxEmb_fst, boxEmb_snd] at h ⊢
  omega

omit [NeZero n] in
theorem boxEmb_surj (r0 c0 m : ℕ) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (x : Cell n)
    (hx : InBox r0 c0 m x) : ∃ x' : Cell m, boxEmb r0 c0 m hr hc x' = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨(⟨x.1.val - r0, by omega⟩, ⟨x.2.val - c0, by omega⟩), ?_⟩
  exact Prod.ext (Fin.ext (by rw [boxEmb_fst]; dsimp only; omega)) (Fin.ext (by rw [boxEmb_snd]; dsimp only; omega))

/-- Local three-cycle: rotate three distinct nonblank cells of a square box of
side `m ≥ 6` containing the blank, in at most `52*m` moves; every other cell
(the blank's included) is fixed. -/
theorem exists_box_three_cycle (B : Board n) (r0 c0 m : ℕ) (hm : 6 ≤ m)
    (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (hbl : InBox r0 c0 m (blank B))
    (a b c : Cell n) (ha : InBox r0 c0 m a) (hb : InBox r0 c0 m b) (hc' : InBox r0 c0 m c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha0 : B a ≠ 0) (hb0 : B b ≠ 0) (hc0 : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C, p.length ≤ 52 * m ∧
      C a = B b ∧ C b = B c ∧ C c = B a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
  have : NeZero m := ⟨by omega⟩
  let ι := boxEmb r0 c0 m hr hc
  obtain ⟨xb, hxb⟩ := boxEmb_surj r0 c0 m hr hc _ hbl
  obtain ⟨a', ha'⟩ := boxEmb_surj r0 c0 m hr hc _ ha
  obtain ⟨b', hb'⟩ := boxEmb_surj r0 c0 m hr hc _ hb
  obtain ⟨c', hc''⟩ := boxEmb_surj r0 c0 m hr hc _ hc'
  let e0 : Cell m ≃ Tile m := finProdFinEquiv
  let e : Cell m ≃ Tile m := e0.trans (Equiv.swap (e0 xb) 0)
  have he : e xb = 0 := by simp [e]
  let η : Tile m ↪ Tile n := ⟨fun t => B (ι (e.symm t)), by
    intro t t' h
    have := ι.injective (B.injective h)
    simpa using this⟩
  have hη0 : η 0 = 0 := by
    change B (ι (e.symm 0)) = 0
    rw [← he, e.symm_apply_apply]
    change B (boxEmb r0 c0 m hr hc xb) = 0
    rw [hxb]
    exact B.apply_symm_apply 0
  have hB : ∀ x, B (ι x) = η (e x) := by
    intro x
    change B (ι x) = B (ι (e.symm (e x)))
    rw [e.symm_apply_apply]
  have hloc0 : ∀ x : Cell m, B (ι x) ≠ 0 → e x ≠ 0 := by
    intro x hx h
    apply hx
    rw [hB, h, hη0]
  have hne : ∀ {x y : Cell m}, ι x ≠ ι y → x ≠ y := fun h h' => h (by rw [h'])
  obtain ⟨D, p, hp, _, hDa, hDb, hDc, hfix⟩ := exists_three_cycle_sharp e hm a' b' c'
    (hne (by change boxEmb _ _ _ _ _ a' ≠ boxEmb _ _ _ _ _ b'; rw [ha', hb']; exact hab))
    (hne (by change boxEmb _ _ _ _ _ a' ≠ boxEmb _ _ _ _ _ c'; rw [ha', hc'']; exact hac))
    (hne (by change boxEmb _ _ _ _ _ b' ≠ boxEmb _ _ _ _ _ c'; rw [hb', hc'']; exact hbc))
    (hloc0 a' (by change B (boxEmb _ _ _ _ _ a') ≠ 0; rw [ha']; exact ha0))
    (hloc0 b' (by change B (boxEmb _ _ _ _ _ b') ≠ 0; rw [hb']; exact hb0))
    (hloc0 c' (by change B (boxEmb _ _ _ _ _ c') ≠ 0; rw [hc'']; exact hc0))
  obtain ⟨C, q, hq, hC, hout⟩ := p.exists_embedded ι (boxEmb_adj r0 c0 m hr hc) η hη0 B hB
  have hι : ∀ x, ι x = boxEmb r0 c0 m hr hc x := fun _ => rfl
  refine ⟨C, q, by omega, ?_, ?_, ?_, ?_⟩
  · rw [← ha', ← hb', ← hι, ← hι, hC, hDa, hB]
  · rw [← hb', ← hc'', ← hι, ← hι, hC, hDb, hB]
  · rw [← hc'', ← ha', ← hι, ← hι, hC, hDc, hB]
  · intro x hxa hxb hxc
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨x', rfl⟩ := hx
      rw [hC, hfix x' (fun h => hxa (by rw [h, hι, ha']))
        (fun h => hxb (by rw [h, hι, hb'])) (fun h => hxc (by rw [h, hι, hc''])), hB]
    · exact hout x hx

/-- The local three-cycle moves only three tiles, each by less than twice the
box side, so at most `28*m` of its moves are inefficient. -/
theorem exists_box_three_cycle_ineff (B : Board n) (r0 c0 m : ℕ) (hm : 6 ≤ m)
    (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (hbl : InBox r0 c0 m (blank B))
    (a b c : Cell n) (ha : InBox r0 c0 m a) (hb : InBox r0 c0 m b) (hc' : InBox r0 c0 m c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha0 : B a ≠ 0) (hb0 : B b ≠ 0) (hc0 : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C, p.inefficientMoves ≤ 28 * m ∧
      C a = B b ∧ C b = B c ∧ C c = B a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
  obtain ⟨C, p, hp, hCa, hCb, hCc, hCx⟩ :=
    exists_box_three_cycle B r0 c0 m hm hr hc hbl a b c ha hb hc' hab hac hbc ha0 hb0 hc0
  refine ⟨C, p, ?_, hCa, hCb, hCc, hCx⟩
  have h := p.two_inefficientMoves_le_of_displacement {a, b, c} (fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hCx x hx.1 hx.2.1 hx.2.2)
  have hpa : position B (C a) = b := by rw [hCa]; simp [position]
  have hpb : position B (C b) = c := by rw [hCb]; simp [position]
  have hpc : position B (C c) = a := by rw [hCc]; simp [position]
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, hpa, hpb, hpc] at h
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  obtain ⟨c1, c2, c3, c4⟩ := hc'
  have hd : gridDistance a b + gridDistance b c + gridDistance c a ≤ 4 * m := by
    simp only [gridDistance, Nat.dist]; omega
  omega


/-! ## Three-cycles near a corner of the box -/

/-- Coordinate `i` of an `m`-box starting at `r0`, reflected when `f`. -/
def reflC (r0 m : ℕ) (f : Bool) (i : ℕ) : ℕ := if f then r0 + (m - 1 - i) else r0 + i

theorem reflC_lt {r0 m : ℕ} (f : Bool) {i : ℕ} (hi : i < m) : reflC r0 m f i < r0 + m := by
  unfold reflC; split_ifs <;> omega

theorem reflC_ge {r0 m : ℕ} (f : Bool) (i : ℕ) : r0 ≤ reflC r0 m f i := by
  unfold reflC; split_ifs <;> omega

theorem dist_reflC {r0 m : ℕ} (f : Bool) {i j : ℕ} (hi : i < m) (hj : j < m) :
    Nat.dist (reflC r0 m f i) (reflC r0 m f j) = Nat.dist i j := by
  unfold reflC; simp only [Nat.dist]; split_ifs <;> omega

omit [NeZero n] in
/-- The embedding of an `m × m` board as the box, reflected in rows (`fr`) and
columns (`fc`), so that the local corner `(0,0)` is any corner of the box. -/
def boxEmbR (r0 c0 m : ℕ) (fr fc : Bool) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) :
    Cell m ↪ Cell n :=
  ⟨fun x => (⟨reflC r0 m fr x.1.val, by have := reflC_lt (r0 := r0) fr x.1.isLt; omega⟩,
      ⟨reflC c0 m fc x.2.val, by have := reflC_lt (r0 := c0) fc x.2.isLt; omega⟩), by
    intro x y h
    have h₁ := congrArg (fun z : Cell n => z.1.val) h
    have h₂ := congrArg (fun z : Cell n => z.2.val) h
    simp only at h₁ h₂
    have e1 := dist_reflC (r0 := r0) fr x.1.isLt y.1.isLt
    have e2 := dist_reflC (r0 := c0) fc x.2.isLt y.2.isLt
    rw [h₁] at e1; rw [h₂] at e2
    simp only [Nat.dist] at e1 e2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))⟩

omit [NeZero n] in
@[simp] theorem boxEmbR_fst (r0 c0 m : ℕ) (fr fc : Bool) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n)
    (x : Cell m) : (boxEmbR r0 c0 m fr fc hr hc x).1.val = reflC r0 m fr x.1.val := rfl

omit [NeZero n] in
@[simp] theorem boxEmbR_snd (r0 c0 m : ℕ) (fr fc : Bool) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n)
    (x : Cell m) : (boxEmbR r0 c0 m fr fc hr hc x).2.val = reflC c0 m fc x.2.val := rfl

omit [NeZero n] in
theorem boxEmbR_dist (r0 c0 m : ℕ) (fr fc : Bool) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n)
    (a b : Cell m) :
    gridDistance (boxEmbR r0 c0 m fr fc hr hc a) (boxEmbR r0 c0 m fr fc hr hc b) =
      gridDistance a b := by
  simp only [gridDistance, boxEmbR_fst, boxEmbR_snd]
  rw [dist_reflC fr a.1.isLt b.1.isLt, dist_reflC fc a.2.isLt b.2.isLt]

omit [NeZero n] in
theorem boxEmbR_surj (r0 c0 m : ℕ) (fr fc : Bool) (hr : r0 + m ≤ n) (hc : c0 + m ≤ n)
    (x : Cell n) (hx : InBox r0 c0 m x) : ∃ x' : Cell m, boxEmbR r0 c0 m fr fc hr hc x' = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨(⟨if fr then m - 1 - (x.1.val - r0) else x.1.val - r0, by split_ifs <;> omega⟩,
    ⟨if fc then m - 1 - (x.2.val - c0) else x.2.val - c0, by split_ifs <;> omega⟩), ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · rw [boxEmbR_fst]; unfold reflC; dsimp only; split_ifs <;> omega
  · rw [boxEmbR_snd]; unfold reflC; dsimp only; split_ifs <;> omega

/-- The distance of the blank and of two cells from the local corner of a
reflected box. -/
def cornerDist (r0 c0 m : ℕ) (fr fc : Bool) (bl a c : Cell n) : ℕ :=
  Nat.dist bl.1.val (reflC r0 m fr 1) + Nat.dist bl.2.val (reflC c0 m fc 0) +
    (Nat.dist a.1.val (reflC r0 m fr 0) + Nat.dist a.2.val (reflC c0 m fc 0)) +
    (Nat.dist c.1.val (reflC r0 m fr 0) + Nat.dist c.2.val (reflC c0 m fc 0))

omit [NeZero n] in
/-- Displacement of a three-cycle with two cells near a corner `(K, L)` of the box. -/
theorem cycle_disp_le {r0 c0 m K L : ℕ} (a b c : Cell n) (hb : InBox r0 c0 m b)
    (hK : r0 ≤ K) (hK' : K < r0 + m) (hL : c0 ≤ L) (hL' : L < c0 + m) :
    gridDistance a b + gridDistance b c + gridDistance c a ≤
      4 * m + 2 * ((Nat.dist a.1.val K + Nat.dist a.2.val L) +
        (Nat.dist c.1.val K + Nat.dist c.2.val L)) := by
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have t1 := Nat.dist.triangle_inequality a.1.val K b.1.val
  have t2 := Nat.dist.triangle_inequality a.2.val L b.2.val
  have t3 := Nat.dist.triangle_inequality b.1.val K c.1.val
  have t4 := Nat.dist.triangle_inequality b.2.val L c.2.val
  have t5 := Nat.dist.triangle_inequality c.1.val K a.1.val
  have t6 := Nat.dist.triangle_inequality c.2.val L a.2.val
  have s1 : Nat.dist K b.1.val ≤ m := by simp only [Nat.dist]; omega
  have s2 : Nat.dist L b.2.val ≤ m := by simp only [Nat.dist]; omega
  have c1 := Nat.dist_comm b.1.val K
  have c2 := Nat.dist_comm b.2.val L
  have c3 := Nat.dist_comm K c.1.val
  have c4 := Nat.dist_comm L c.2.val
  have c5 := Nat.dist_comm K a.1.val
  have c6 := Nat.dist_comm L a.2.val
  unfold gridDistance
  omega

set_option maxHeartbeats 1000000 in
/-- Local three-cycle with `a` and `c` near the corner of the box selected by
`fr, fc`, at most `10 m + 82 δ + 436` of its moves inefficient. -/
theorem exists_box_three_cycle_near (B : Board n) (r0 c0 m : ℕ) (fr fc : Bool) (hm : 6 ≤ m)
    (hr : r0 + m ≤ n) (hc : c0 + m ≤ n) (hbl : InBox r0 c0 m (blank B))
    (a b c : Cell n) (ha : InBox r0 c0 m a) (hb : InBox r0 c0 m b) (hc' : InBox r0 c0 m c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha0 : B a ≠ 0) (hb0 : B b ≠ 0) (hc0 : B c ≠ 0) :
    ∃ C : Board n, ∃ p : Path B C,
      p.inefficientMoves ≤ 10 * m + 82 * cornerDist r0 c0 m fr fc (blank B) a c + 436 ∧
      C a = B b ∧ C b = B c ∧ C c = B a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
  have : NeZero m := ⟨by omega⟩
  let ι := boxEmbR r0 c0 m fr fc hr hc
  have hι : ∀ x, ι x = boxEmbR r0 c0 m fr fc hr hc x := fun _ => rfl
  obtain ⟨xb, hxb⟩ := boxEmbR_surj r0 c0 m fr fc hr hc _ hbl
  obtain ⟨a', ha'⟩ := boxEmbR_surj r0 c0 m fr fc hr hc _ ha
  obtain ⟨b', hb'⟩ := boxEmbR_surj r0 c0 m fr fc hr hc _ hb
  obtain ⟨c', hc''⟩ := boxEmbR_surj r0 c0 m fr fc hr hc _ hc'
  let e0 : Cell m ≃ Tile m := finProdFinEquiv
  let e : Cell m ≃ Tile m := e0.trans (Equiv.swap (e0 xb) 0)
  have he : e xb = 0 := by simp [e]
  have heb : blank e = xb := by
    change e.symm 0 = xb
    rw [← he, e.symm_apply_apply]
  let η : Tile m ↪ Tile n := ⟨fun t => B (ι (e.symm t)), by
    intro t t' h
    have := ι.injective (B.injective h)
    simpa using this⟩
  have hη0 : η 0 = 0 := by
    change B (ι (e.symm 0)) = 0
    rw [← he, e.symm_apply_apply, hι, hxb]
    exact B.apply_symm_apply 0
  have hB : ∀ x, B (ι x) = η (e x) := by
    intro x
    change B (ι x) = B (ι (e.symm (e x)))
    rw [e.symm_apply_apply]
  have hloc0 : ∀ x : Cell m, B (ι x) ≠ 0 → e x ≠ 0 := by
    intro x hx h
    apply hx
    rw [hB, h, hη0]
  have hne : ∀ {x y : Cell m}, ι x ≠ ι y → x ≠ y := fun h h' => h (by rw [h'])
  obtain ⟨D, p, hp, _, hDa, hDb, hDc, hfix⟩ := exists_three_cycle_near e hm a' b' c'
    (hne (by rw [hι, hι, ha', hb']; exact hab))
    (hne (by rw [hι, hι, ha', hc'']; exact hac))
    (hne (by rw [hι, hι, hb', hc'']; exact hbc))
    (hloc0 a' (by rw [hι, ha']; exact ha0))
    (hloc0 b' (by rw [hι, hb']; exact hb0))
    (hloc0 c' (by rw [hι, hc'']; exact hc0))
  obtain ⟨C, q, hq, hC, hout⟩ := p.exists_embedded ι
    (fun x y h => by rw [hι, hι, boxEmbR_dist]; exact h) η hη0 B hB
  -- the local distances are the distances in the box
  have hδ : gridDistance (blank e) ((⟨1, by omega⟩ : Fin m), (⟨0, by omega⟩ : Fin m)) +
      gridDistance a' ((⟨0, by omega⟩ : Fin m), (⟨0, by omega⟩ : Fin m)) +
      gridDistance c' ((⟨0, by omega⟩ : Fin m), (⟨0, by omega⟩ : Fin m)) =
      cornerDist r0 c0 m fr fc (blank B) a c := by
    rw [heb, ← boxEmbR_dist r0 c0 m fr fc hr hc xb, ← boxEmbR_dist r0 c0 m fr fc hr hc a',
      ← boxEmbR_dist r0 c0 m fr fc hr hc c', hxb, ha', hc'']
    unfold cornerDist gridDistance
    simp only [boxEmbR_fst, boxEmbR_snd]
  have hCa : C a = B b := by rw [← ha', ← hb', ← hι, ← hι, hC, hDa, hB]
  have hCb : C b = B c := by rw [← hb', ← hc'', ← hι, ← hι, hC, hDb, hB]
  have hCc : C c = B a := by rw [← hc'', ← ha', ← hι, ← hι, hC, hDc, hB]
  have hCx : ∀ x, x ≠ a → x ≠ b → x ≠ c → C x = B x := by
    intro x hxa hxb hxc
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨x', rfl⟩ := hx
      rw [hC, hfix x' (fun h => hxa (by rw [h, hι, ha']))
        (fun h => hxb (by rw [h, hι, hb'])) (fun h => hxc (by rw [h, hι, hc''])), hB]
    · exact hout x hx
  refine ⟨C, q, ?_, hCa, hCb, hCc, hCx⟩
  have h := q.two_inefficientMoves_le_of_displacement {a, b, c} (fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hCx x hx.1 hx.2.1 hx.2.2)
  have hpa : position B (C a) = b := by rw [hCa]; simp [position]
  have hpb : position B (C b) = c := by rw [hCb]; simp [position]
  have hpc : position B (C c) = a := by rw [hCc]; simp [position]
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, hpa, hpb, hpc] at h
  -- displacement: `b` is within `2m` of the corner, `a` and `c` are near it
  have hK := reflC_lt (r0 := r0) (m := m) fr (i := 0) (by omega)
  have hK' := reflC_ge (r0 := r0) (m := m) fr 0
  have hL := reflC_lt (r0 := c0) (m := m) fc (i := 0) (by omega)
  have hL' := reflC_ge (r0 := c0) (m := m) fc 0
  have hd := cycle_disp_le a b c hb hK' hK hL' hL
  have hδ' : (Nat.dist a.1.val (reflC r0 m fr 0) + Nat.dist a.2.val (reflC c0 m fc 0)) +
      (Nat.dist c.1.val (reflC r0 m fr 0) + Nat.dist c.2.val (reflC c0 m fc 0)) ≤
      cornerDist r0 c0 m fr fc (blank B) a c := by
    unfold cornerDist; omega
  rw [hδ] at hp
  rw [hq] at h
  generalize cornerDist r0 c0 m fr fc (blank B) a c = δ at *
  generalize gridDistance a b = d1 at *
  generalize gridDistance b c = d2 at *
  generalize gridDistance c a = d3 at *
  generalize q.inefficientMoves = I at *
  generalize p.length = P at *
  omega

end SlidingPuzzle.Hub
