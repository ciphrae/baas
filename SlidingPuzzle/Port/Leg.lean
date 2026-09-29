import SlidingPuzzle.Port.Xfer

/-! # Relocation legs between aligned squares

The blank sits in the box of port `b` of square `E`; `Z` is in the same band
(`hor`) or block column. From the box cell `a0` of `E` nearest its corner the blank
jumps to the aligned cell `z0` of `Z`'s box of port `b` (the tile there goes to `a0`),
lines up the carried tile on `z1` (two cells deeper) by three-cycles staged at `Z`'s
corner, jumps back and jumps to `z1`. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf sqDist apply_blank blank_eq_of_apply
  val_ne_zero_of_ne_blank exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist
  InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} (L : LaneSys k q)

/-- The cell of `Z`'s box reached by the first jump, shifted `m` cells deeper, before the
parity shift `j` (perpendicular to the jump). -/
def lz (k s : ℕ) (b : Pt) (hor : Bool) (j m : ℕ) : ℕ × ℕ :=
  match b, hor with
  | .tl, true => (k + 1 + j, k + 1 + m)
  | .tr, true => (k + 1 + j, s - 2 - m)
  | .bl, true => (s - 2 - j, k + 1 + m)
  | .tl, false => (k + 1 + m, k + 1 + j)
  | .tr, false => (k + 1 + m, s - 2 - j)
  | .bl, false => (s - 2 - m, k + 1 + j)

/-- Geometry of a leg, in local coordinates. -/
theorem lgeom (h8 : 8 ≤ σ) (hs : 2 * σ + 2 * k + 8 ≤ s) (b : Pt) (hor : Bool) {j m : ℕ}
    (hj : j ≤ 1) (hm : m ≤ 4) :
    inBox k s σ b (ncell k s b).1 (ncell k s b).2 ∧
    inBox k s σ b (lz k s b hor j m).1 (lz k s b hor j m).2 ∧
    (∀ i : Fin 3, spare k s b i ≠ lz k s b hor j m) ∧
    (hor = true → (lz k s b hor j m).1 ≤ (ncell k s b).1 + 1 ∧
      (ncell k s b).1 ≤ (lz k s b hor j m).1 + 1 ∧
      ((ncell k s b).1 + (lz k s b hor j m).1) % 2 = j % 2 ∧
      ((ncell k s b).2 + (lz k s b hor j m).2) % 2 = m % 2 ∧
      Nat.dist (ncell k s b).2 (lz k s b hor j m).2 ≤ m) ∧
    (hor = false → (lz k s b hor j m).2 ≤ (ncell k s b).2 + 1 ∧
      (ncell k s b).2 ≤ (lz k s b hor j m).2 + 1 ∧
      ((ncell k s b).2 + (lz k s b hor j m).2) % 2 = j % 2 ∧
      ((ncell k s b).1 + (lz k s b hor j m).1) % 2 = m % 2 ∧
      Nat.dist (ncell k s b).1 (lz k s b hor j m).1 ≤ m) ∧
    cdist k s σ b (lz k s b hor j m).1 (lz k s b hor j m).2 ≤ 2 * k + 8 ∧
    (ncell k s b).1 < s ∧ (ncell k s b).2 < s ∧ (lz k s b hor j m).1 < s ∧
      (lz k s b hor j m).2 < s := by
  cases b <;> cases hor <;>
    simp only [ncell, lz, inBox, spare, cdist, cfr, cfc, ne_eq, Prod.mk.injEq, if_true, if_false,
      Bool.false_eq_true, Nat.dist, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_implies] <;>
    refine ⟨?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try have := i.isLt) <;>
    (try split_ifs) <;> (try and_intros) <;> first | omega | trivial

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf sqDist apply_blank blank_eq_of_apply
  val_ne_zero_of_ne_blank exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist
  InBox)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

theorem dist_mul_add {a b s r c : ℕ} (hr : r < s) (hc : c < s) :
    Nat.dist (a * s + r) (b * s + c) ≤ Nat.dist a b * s + Nat.dist r c := by
  rcases le_total a b with h | h
  · have e : Nat.dist a b * s = b * s - a * s := by
      unfold Nat.dist; rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.sub_mul]
    have := Nat.mul_le_mul_right s h
    rw [e]; simp only [Nat.dist] at *; omega
  · have e : Nat.dist a b * s = a * s - b * s := by
      unfold Nat.dist; rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.sub_mul]
    have := Nat.mul_le_mul_right s h
    rw [e]; simp only [Nat.dist] at *; omega

/-- A jump between local cells of two aligned squares. -/
theorem jump_cross (pd : PDims n k s q σ) (E Z : Sq k) {r1 c1 r2 c2 : ℕ} (h1 : r1 < s) (h2 : c1 < s)
    (h3 : r2 < s) (h4 : c2 < s)
    (hal : (E.1 = Z.1 ∧ r1 ≤ r2 + 1 ∧ r2 ≤ r1 + 1) ∨ (E.2 = Z.2 ∧ c1 ≤ c2 + 1 ∧ c2 ≤ c1 + 1))
    (hpar : (E.1.val * s + r1 + (E.2.val * s + c1) + (Z.1.val * s + r2) + (Z.2.val * s + c2)) % 2 = 1)
    (hd : Nat.dist r1 r2 ≤ 4 ∧ Nat.dist c1 c2 ≤ 4) (B' : Board n) (hB' : blank B' = lc s E r1 c1) :
    ∃ p : Path B' (swapCells B' (blank B') (lc s Z r2 c2)),
      p.inefficientMoves ≤ 7 * (sqDist E Z * s + 5) := by
  have a1 := lc_fst (n := n) pd.hd E c1 h1
  have a2 := lc_snd (n := n) pd.hd E r1 h2
  have b1 := lc_fst (n := n) pd.hd Z c2 h3
  have b2 := lc_snd (n := n) pd.hd Z r2 h4
  have d1 := dist_mul_add (a := E.1.val) (b := Z.1.val) h1 h3
  have d2 := dist_mul_add (a := E.2.val) (b := Z.2.val) h2 h4
  have hsd : Nat.dist E.1.val Z.1.val * s + Nat.dist E.2.val Z.2.val * s = sqDist E Z * s := by
    unfold sqDist; ring
  rcases hal with ⟨he, hr⟩ | ⟨he, hc⟩
  · have e1 : E.1.val = Z.1.val := congrArg Fin.val he
    obtain ⟨p, hp⟩ := exists_hjump_step pd.hd.two_le_n B' (lc s Z r2 c2)
      (by rw [hB', a1, b1, e1]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    refine ⟨p, hp.trans ?_⟩
    rw [hB', a2, b2]
    have : Nat.dist E.1.val Z.1.val = 0 := by rw [e1]; simp [Nat.dist]
    rw [this, zero_mul, zero_add] at hsd
    have := Nat.mul_le_mul_left 7 (d2.trans (Nat.add_le_add_left hd.2 _))
    rw [hsd] at this
    omega
  · have e2 : E.2.val = Z.2.val := congrArg Fin.val he
    obtain ⟨p, hp⟩ := exists_vjump_step pd.hd.two_le_n B' (lc s Z r2 c2)
      (by rw [hB', a2, b2, e2]; simp only [Nat.dist]; omega)
      (by rw [hB', a1, a2, b1, b2]; omega)
    refine ⟨p, hp.trans ?_⟩
    rw [hB', a1, b1]
    have : Nat.dist E.2.val Z.2.val = 0 := by rw [e2]; simp [Nat.dist]
    rw [this, zero_mul, add_zero] at hsd
    have := Nat.mul_le_mul_left 7 (d1.trans (Nat.add_le_add_left hd.1 _))
    rw [hsd] at this
    omega

end SlidingPuzzle.Port

namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf)
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} [NeZero n] (L : LaneSys k q)

theorem ind_some {Q A : Sq k} {pt' : Pt} {a : Part} {c z' : Sq k} :
    (some (A, a) = some (Q, some pt') ∧ c = z') ↔
      (((Q, some pt', z') : Sq k × Part × Sq k) = (A, a, c)) := by
  simp only [Option.some.injEq, Prod.mk.injEq]; tauto

theorem ind_goal {Q A : Sq k} {pt' a : Pt} {c z' : Sq k} :
    (Q = A ∧ pt' = a ∧ z' = c) ↔ (((Q, some pt', z') : Sq k × Part × Sq k) = (A, some a, c)) := by
  simp only [Prod.mk.injEq, Option.some.injEq]

/-- Port counts through a leg carrying a tile from `Z`'s port `b` to `E`'s. -/
theorem pc_legA (pd : PDims n k s q σ) {B C : Board n} {Y : Tile n} {E Z : Sq k} {b : Pt}
    (hEZ : E ≠ Z) (K : KeepK (rkey L s σ pd.hd) B C {Y}) (hY0 : Y.val ≠ 0)
    (hB : rkey L s σ pd.hd (position B Y) = some (Z, some b))
    (hC : rkey L s σ pd.hd (position C Y) = some (E, some b)) :
    pcOf L pd C = decP (incP (pcOf L pd B) E b (classOf pd.hd Y)) Z b (classOf pd.hd Y) := by
  funext Q pt' z'
  have e := kcount_move1 (rkey L s σ pd.hd) pd.hd K hY0 (some (Q, some pt')) z'
  rw [hB, hC] at e
  simp only [ind_some] at e
  unfold pcOf pcount decP incP at *
  simp only [ind_goal]
  set τ : Sq k × Part × Sq k := (Q, some pt', z') with hτ
  set c := classOf pd.hd Y
  have hd : ((E, (some b : Part), c) : Sq k × Part × Sq k) ≠ (Z, some b, c) := by
    simp [Prod.ext_iff, hEZ]
  by_cases h1 : τ = (E, some b, c)
  · have h2 : ¬ τ = (Z, some b, c) := fun h => hd (h1.symm.trans h)
    simp only [h1, h2, if_true, if_false] at e ⊢
    omega
  · by_cases h2 : τ = (Z, some b, c)
    · simp only [h1, h2, if_true, if_false] at e ⊢
      omega
    · simp only [h1, h2, if_false] at e ⊢
      omega

/-- Port counts through a leg carrying a tile from part `p ≠ b` of `Z`, a tile of `Z`'s port `b`
going to part `p` in exchange. -/
theorem pc_legB (pd : PDims n k s q σ) {B C : Board n} {Y T : Tile n} {E Z : Sq k} {b : Pt}
    {p : Part} (hp : p ≠ some b) (hEZ : E ≠ Z) (K : KeepK (rkey L s σ pd.hd) B C {Y, T})
    (hYT : Y ≠ T) (hY0 : Y.val ≠ 0) (hT0 : T.val ≠ 0)
    (hYB : rkey L s σ pd.hd (position B Y) = some (Z, p))
    (hYC : rkey L s σ pd.hd (position C Y) = some (E, some b))
    (hTB : rkey L s σ pd.hd (position B T) = some (Z, some b))
    (hTC : rkey L s σ pd.hd (position C T) = some (Z, p))
    (hpos : ∀ p' : Pt, p = some p' → 1 ≤ pcOf L pd B Z p' (classOf pd.hd Y)) :
    pcOf L pd C = PState.legPc (incP (pcOf L pd B) E b (classOf pd.hd Y)) Z b (classOf pd.hd Y) p
      (classOf pd.hd T) := by
  funext Q pt' z'
  have e := kcount_move2 (rkey L s σ pd.hd) pd.hd K hYT hY0 hT0 (some (Q, some pt')) z'
  rw [hYB, hYC, hTB, hTC] at e
  simp only [ind_some] at e
  generalize classOf pd.hd Y = y at *
  generalize classOf pd.hd T = z at *
  have hEb : ∀ (a : Part) (c c' : Sq k), ((E, (some b : Part), c) : Sq k × Part × Sq k) ≠ (Z, a, c') := by
    intro a c c'; simp [Prod.ext_iff, hEZ]
  cases p with
  | none =>
    show pcOf L pd C Q pt' z' = decP (incP (pcOf L pd B) E b y) Z b z Q pt' z'
    unfold pcOf pcount decP incP
    simp only [ind_goal]
    have hn : ∀ c : Sq k, ¬ (((Q, some pt', z') : Sq k × Part × Sq k) = (Z, none, c)) := by
      intro c h; simp [Prod.ext_iff] at h
    generalize ((Q, some pt', z') : Sq k × Part × Sq k) = τ at *
    rw [if_neg (hn y), if_neg (hn z)] at e
    by_cases h1 : τ = (E, some b, y)
    · rw [if_pos h1, if_neg (fun h => hEb _ _ _ (h1.symm.trans h))] at e ⊢
      omega
    · by_cases h2 : τ = (Z, some b, z)
      · rw [if_neg h1, if_pos h2] at e ⊢
        omega
      · rw [if_neg h1, if_neg h2] at e ⊢
        omega
  | some p' =>
    have hp' : p' ≠ b := fun h => hp (by rw [h])
    show pcOf L pd C Q pt' z' = (if p' = b then decP (incP (pcOf L pd B) E b y) Z b y
      else decP (incP (decP (incP (pcOf L pd B) E b y) Z p' y) Z p' z) Z b z) Q pt' z'
    rw [if_neg hp']
    have hq : ((Q, some pt', z') : Sq k × Part × Sq k) = (Z, some p', y) →
        1 ≤ kcount (rkey L s σ pd.hd) pd.hd B (some (Q, some pt')) z' := by
      intro h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hpos pt' rfl
    unfold pcOf pcount decP incP
    simp only [ind_goal]
    generalize ((Q, some pt', z') : Sq k × Part × Sq k) = τ at *
    have d1 : ((Z, (some p' : Part), y) : Sq k × Part × Sq k) ≠ (Z, some b, z) := by
      simp [Prod.ext_iff, hp']
    have d2 : ((Z, (some b : Part), z) : Sq k × Part × Sq k) ≠ (Z, some p', z) := by
      simp [Prod.ext_iff, Ne.symm hp']
    by_cases h1 : τ = (E, some b, y)
    · rw [if_pos h1, if_neg (fun h => hEb _ _ _ (h1.symm.trans h)),
        if_neg (fun h => hEb _ _ _ (h1.symm.trans h)),
        if_neg (fun h => hEb _ _ _ (h1.symm.trans h))] at e ⊢
      omega
    · rw [if_neg h1] at e ⊢
      by_cases h2 : τ = (Z, some p', y)
      · have h3 : ¬ τ = (Z, some b, z) := fun h => d1 (h2.symm.trans h)
        have := hq h2
        rw [if_pos h2, if_neg h3] at e ⊢
        by_cases h4 : τ = (Z, some p', z)
        · rw [if_pos h4] at e ⊢; omega
        · rw [if_neg h4] at e ⊢; omega
      · rw [if_neg h2] at e ⊢
        by_cases h3 : τ = (Z, some b, z)
        · have h4 : ¬ τ = (Z, some p', z) := fun h => d2 (h3.symm.trans h)
          rw [if_pos h3, if_neg h4] at e ⊢; omega
        · rw [if_neg h3] at e ⊢
          by_cases h4 : τ = (Z, some p', z)
          · rw [if_pos h4] at e ⊢; omega
          · rw [if_neg h4] at e ⊢; omega

end SlidingPuzzle.Port
