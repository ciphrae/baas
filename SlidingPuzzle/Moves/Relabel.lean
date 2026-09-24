import SlidingPuzzle.Moves.Placement

/-! Relabeling tile names by a permutation which fixes the blank. -/
namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- Rename every tile on a board. -/
def relabel (B : Board n) (e : Equiv.Perm (Tile n)) : Board n := B.trans e

@[simp] theorem relabel_apply (B : Board n) (e : Equiv.Perm (Tile n)) (c : Cell n) :
    relabel B e c = e (B c) := rfl

theorem relabel_swapCells (B : Board n) (e : Equiv.Perm (Tile n)) (a b : Cell n) :
    relabel (swapCells B a b) e = swapCells (relabel B e) a b := by
  ext c
  rfl

theorem blank_relabel (B : Board n) (e : Equiv.Perm (Tile n)) (he : e 0 = 0) :
    blank (relabel B e) = blank B := by
  have hesymm : e.symm 0 = 0 := by
    apply e.injective
    simpa [he] using e.apply_symm_apply 0
  simp [blank, position, relabel, hesymm]

theorem Step.relabel {B C : Board n} (e : Equiv.Perm (Tile n)) (he : e 0 = 0)
    (h : Step B C) : Step (relabel B e) (relabel C e) := by
  obtain ⟨c, hc, hC⟩ := h
  refine ⟨c, ?_, ?_⟩
  · simpa [blank_relabel B e he] using hc
  · rw [hC, relabel_swapCells]
    simp [blank_relabel B e he]

def Path.relabel {B C : Board n} : (p : Path B C) → (e : Equiv.Perm (Tile n)) → (he : e 0 = 0) →
    Path (_root_.SlidingPuzzle.relabel B e) (_root_.SlidingPuzzle.relabel C e)
  | .nil B, e, _ => .nil (_root_.SlidingPuzzle.relabel B e)
  | .cons h p, e, he => .cons (h.relabel e he) (p.relabel e he)

@[simp] theorem Path.length_relabel {B C : Board n} (p : Path B C)
    (e : Equiv.Perm (Tile n)) (he : e 0 = 0) : (p.relabel e he).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [Path.relabel, ih]

theorem relabel_relabel_symm (B : Board n) (e : Equiv.Perm (Tile n)) :
    relabel (relabel B e) e.symm = B := by
  ext c
  simp [relabel]

private theorem target_relabel_perm (T : Board n)
    (hblank : blank T = blank (target n)) :
    let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
    e 0 = 0 := by
  dsimp
  have hpos : T.symm 0 = (target n).symm 0 := by
    simpa [blank, position] using hblank
  rw [hpos]
  exact (target n).apply_symm_apply 0

private theorem relabel_to_target (B T : Board n)
    (e : Equiv.Perm (Tile n)) (he : e = T.symm.trans (target n))
    {c : Cell n} (h : B c = T c) : relabel B e c = target n c := by
  subst e
  change target n (T.symm (B c)) = target n c
  rw [h]
  simp

private theorem inverse_relabel_target (T : Board n) (e : Equiv.Perm (Tile n))
    (he : e = T.symm.trans (target n)) (c : Cell n) :
    relabel (target n) e.symm c = T c := by
  subst e
  simp [relabel]

/-- The protected-row placement theorem with any target whose blank is in the
standard blank cell. -/
theorem exists_protected_row_path_relabel
    (r : ℕ) (hr : r + 1 < n) (hr2 : r + 2 < n) (hm : 4 ≤ n)
    (lo : ℕ) (hlo : lo + 4 ≤ n) (B T : Board n)
    (hblank : blank T = blank (target n))
    (habove : ∀ (x y : Fin n), x.val < r → B (x, y) = T (x, y))
    (hcol : ∀ (x y : Fin n), y.val < lo → B (x, y) = T (x, y)) :
    ∃ (C : Board n) (p : Path B C),
      p.length ≤ (n - lo) * (251 * (n + n)) ∧
      (∀ (x y : Fin n), x.val < r → C (x, y) = B (x, y)) ∧
      (∀ (x y : Fin n), y.val < lo → C (x, y) = B (x, y)) ∧
      (∀ y : Fin n, C ((⟨r, by omega⟩ : Fin n), y) = T ((⟨r, by omega⟩ : Fin n), y)) := by
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e = T.symm.trans (target n) := rfl
  have hezero : e 0 = 0 := target_relabel_perm T hblank
  have hesymmzero : e.symm 0 = 0 := by
    apply e.injective
    simpa [hezero] using e.apply_symm_apply 0
  obtain ⟨D, p, hp, hpabove, hpcol, hprow⟩ :=
    exists_protected_row_path r hr hr2 hm lo hlo (relabel B e)
      (fun x y hx => relabel_to_target B T e he (habove x y hx))
      (fun x y hy => relabel_to_target B T e he (hcol x y hy))
  have hq : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
      q.length ≤ (n-lo)*(251*(n+n)) :=
    ⟨p.relabel e.symm hesymmzero, by simpa using hp⟩
  rw [relabel_relabel_symm] at hq
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm, q, hq, ?_, ?_, ?_⟩
  · intro x y hx
    have h := congrArg e.symm (hpabove x y hx)
    simpa [relabel] using h
  · intro x y hy
    have h := congrArg e.symm (hpcol x y hy)
    simpa [relabel] using h
  · intro y
    have h := congrArg e.symm (hprow y)
    calc
      relabel D e.symm ((⟨r, by omega⟩ : Fin n), y) =
          e.symm (D ((⟨r, by omega⟩ : Fin n), y)) := rfl
      _ = e.symm (target n ((⟨r, by omega⟩ : Fin n), y)) := h
      _ = relabel (target n) e.symm ((⟨r, by omega⟩ : Fin n), y) := rfl
      _ = T ((⟨r, by omega⟩ : Fin n), y) := inverse_relabel_target T e he _

/-- The protected-column placement theorem with any target whose blank is in the
standard blank cell. -/
theorem exists_protected_column_path_relabel
    (r : ℕ) (hr : r + 2 < n) (hlo : r + 4 ≤ n) (B T : Board n)
    (hblank : blank T = blank (target n))
    (habove : ∀ (x y : Fin n), x.val < r → B (x, y) = T (x, y))
    (hcol : ∀ (x y : Fin n), y.val < r → B (x, y) = T (x, y)) :
    ∃ (C : Board n) (p : Path B C),
      p.length ≤ (n - r) * (251 * (n + n)) ∧
      (∀ (x y : Fin n), x.val < r → C (x, y) = B (x, y)) ∧
      (∀ (x y : Fin n), y.val < r → C (x, y) = B (x, y)) ∧
      (∀ x : Fin n, C (x, (⟨r, by omega⟩ : Fin n)) = T (x, (⟨r, by omega⟩ : Fin n))) := by
  let e : Equiv.Perm (Tile n) := T.symm.trans (target n)
  have he : e = T.symm.trans (target n) := rfl
  have hezero : e 0 = 0 := target_relabel_perm T hblank
  have hesymmzero : e.symm 0 = 0 := by
    apply e.injective
    simpa [hezero] using e.apply_symm_apply 0
  obtain ⟨D, p, hp, hpabove, hpcol, hprow⟩ :=
    exists_protected_column_path r hr hlo (relabel B e)
      (fun x y hx => relabel_to_target B T e he (habove x y hx))
      (fun x y hy => relabel_to_target B T e he (hcol x y hy))
  have hq : ∃ q : Path (relabel (relabel B e) e.symm) (relabel D e.symm),
      q.length ≤ (n-r)*(251*(n+n)) :=
    ⟨p.relabel e.symm hesymmzero, by simpa using hp⟩
  rw [relabel_relabel_symm] at hq
  obtain ⟨q,hq⟩ := hq
  refine ⟨relabel D e.symm, q, hq, ?_, ?_, ?_⟩
  · intro x y hx
    have h := congrArg e.symm (hpabove x y hx)
    simpa [relabel] using h
  · intro x y hy
    have h := congrArg e.symm (hpcol x y hy)
    simpa [relabel] using h
  · intro y
    have h := congrArg e.symm (hprow y)
    calc
      relabel D e.symm (y, (⟨r, by omega⟩ : Fin n)) =
          e.symm (D (y, (⟨r, by omega⟩ : Fin n))) := rfl
      _ = e.symm (target n (y, (⟨r, by omega⟩ : Fin n))) := h
      _ = relabel (target n) e.symm (y, (⟨r, by omega⟩ : Fin n)) := rfl
      _ = T (y, (⟨r, by omega⟩ : Fin n)) := inverse_relabel_target T e he _

end SlidingPuzzle
