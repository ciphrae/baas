import SlidingPuzzle.Moves.Relabel
import SlidingPuzzle.Algorithm.Accounting

/-! Access, a local blank-returning operation, and reversed access. -/
namespace SlidingPuzzle
variable {n : ℕ} [NeZero n]

/-- Undo arbitrary staging after a blank-returning local operation. The resulting
effect is transported back to the original positions of the staged tiles. -/
theorem Path.exists_unstaged {B C D : Board n} (p : Path B C) (q : Path C D)
    (hblank : blank D = blank C) :
    ∃ E : Board n, ∃ r : Path B E,
      r.length = 2*p.length + q.length ∧ blank E = blank B ∧
      ∀ x, E x = D (C.symm (B x)) := by
  let e : Equiv.Perm (Tile n) := C.symm.trans D
  have he : e 0 = 0 := by
    change D (blank C) = 0
    rw [← hblank]
    simp [blank, position]
  have hC : SlidingPuzzle.relabel C e = D := by
    ext x
    simp [SlidingPuzzle.relabel, e]
  have hret : ∃ s : Path D (SlidingPuzzle.relabel B e), s.length = p.length := by
    have h : ∃ s : Path (SlidingPuzzle.relabel C e) (SlidingPuzzle.relabel B e),
        s.length = p.length := ⟨p.reverse.relabel e he, by simp⟩
    rwa [hC] at h
  obtain ⟨s, hs⟩ := hret
  refine ⟨SlidingPuzzle.relabel B e, (p.append q).append s, ?_,
    blank_relabel B e he, fun _ => rfl⟩
  simp only [Path.length_append, hs]
  omega

/-- Undo access after an operation that returns the blank. If access fixes the
operation's support, its effect there survives and every outside cell is restored. -/
theorem Path.exists_conjugated {B C D : Board n} (p : Path B C) (q : Path C D)
    (hblank : blank D = blank C) (S : Set (Cell n))
    (haccess : ∀ x ∈ S, C x = B x) (hlocal : ∀ x ∉ S, D x = C x) :
    ∃ E : Board n, ∃ r : Path B E,
      r.length = 2*p.length + q.length ∧ blank E = blank B ∧
      (∀ x ∈ S, E x = D x) ∧ (∀ x ∉ S, E x = B x) := by
  let e : Equiv.Perm (Tile n) := C.symm.trans D
  have he : e 0 = 0 := by
    change D (blank C) = 0
    rw [← hblank]
    simp [blank, position]
  have hC : SlidingPuzzle.relabel C e = D := by ext x; simp [SlidingPuzzle.relabel, e]
  have hret : ∃ s : Path D (SlidingPuzzle.relabel B e), s.length = p.length := by
    have h : ∃ s : Path (SlidingPuzzle.relabel C e) (SlidingPuzzle.relabel B e), s.length = p.length :=
      ⟨p.reverse.relabel e he, by simp⟩
    rwa [hC] at h
  obtain ⟨s,hs⟩ := hret
  refine ⟨SlidingPuzzle.relabel B e,(p.append q).append s,?_,blank_relabel B e he,?_,?_⟩
  · simp only [Path.length_append, hs]; omega
  · intro x hx
    change D (C.symm (B x)) = D x
    rw [← haccess x hx, C.symm_apply_apply]
  · intro x hx
    have hnot : C.symm (B x) ∉ S := by
      intro hc
      have hh := haccess (C.symm (B x)) hc
      rw [C.apply_symm_apply] at hh
      have heq : x = C.symm (B x) := B.injective hh
      exact hx (heq.symm ▸ hc)
    change D (C.symm (B x)) = B x
    rw [hlocal _ hnot, C.apply_symm_apply]

/-- `exists_conjugated` with inefficiency: the access and its reversal are
charged by length, the operation by its own inefficiency. -/
theorem Path.exists_conjugated_efficient {B C D : Board n} (p : Path B C) (q : Path C D)
    (hblank : blank D = blank C) (S : Set (Cell n))
    (haccess : ∀ x ∈ S, C x = B x) (hlocal : ∀ x ∉ S, D x = C x) :
    ∃ E : Board n, ∃ r : Path B E,
      r.length = 2*p.length + q.length ∧
      r.inefficientMoves ≤ 2*p.length + q.inefficientMoves ∧ blank E = blank B ∧
      (∀ x ∈ S, E x = D x) ∧ (∀ x ∉ S, E x = B x) := by
  let e : Equiv.Perm (Tile n) := C.symm.trans D
  have he : e 0 = 0 := by
    change D (blank C) = 0
    rw [← hblank]
    simp [blank, position]
  have hC : SlidingPuzzle.relabel C e = D := by ext x; simp [SlidingPuzzle.relabel, e]
  have hret : ∃ s : Path D (SlidingPuzzle.relabel B e), s.length = p.length := by
    have h : ∃ s : Path (SlidingPuzzle.relabel C e) (SlidingPuzzle.relabel B e), s.length = p.length :=
      ⟨p.reverse.relabel e he, by simp⟩
    rwa [hC] at h
  obtain ⟨s,hs⟩ := hret
  refine ⟨SlidingPuzzle.relabel B e,(p.append q).append s,?_,?_,blank_relabel B e he,?_,?_⟩
  · simp only [Path.length_append, hs]; omega
  · simp only [Path.inefficientMoves_append]
    have h₁ := p.inefficientMoves_le_length
    have h₂ := s.inefficientMoves_le_length
    omega
  · intro x hx
    change D (C.symm (B x)) = D x
    rw [← haccess x hx, C.symm_apply_apply]
  · intro x hx
    have hnot : C.symm (B x) ∉ S := by
      intro hc
      have hh := haccess (C.symm (B x)) hc
      rw [C.apply_symm_apply] at hh
      have heq : x = C.symm (B x) := B.injective hh
      exact hx (heq.symm ▸ hc)
    change D (C.symm (B x)) = B x
    rw [hlocal _ hnot, C.apply_symm_apply]

end SlidingPuzzle
