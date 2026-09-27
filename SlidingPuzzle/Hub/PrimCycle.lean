import SlidingPuzzle.Moves.ThreeCycleSharp
import SlidingPuzzle.Moves.Embedding

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

end SlidingPuzzle.Hub
