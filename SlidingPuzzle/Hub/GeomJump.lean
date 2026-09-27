import SlidingPuzzle.Hub.PrimRes
import SlidingPuzzle.Hub.PrimWalk

/-! # Geometry of jumps between aligned squares

A square box of side `(1 + sqDist E Z) * s` inside the board covers both
squares, and a straight jump connects a reservoir cell of `E` with a reservoir
cell of `Z`. -/
namespace SlidingPuzzle.Hub

variable {n k s : ℕ} [NeZero n]

omit [NeZero n] in
/-- An interval of length `m ≥ (dist a b + 1) * s` inside `[0, n)` covering the
bands `a` and `b`. -/
theorem interval_cover (hd : HDims n k s) {a b m : ℕ} (ha : a < k) (hb : b < k)
    (hm1 : (Nat.dist a b + 1) * s ≤ m) (hm2 : m ≤ n) :
    ∃ r0, r0 + m ≤ n ∧ r0 ≤ a * s ∧ r0 ≤ b * s ∧ a * s + s ≤ r0 + m ∧ b * s + s ≤ r0 + m := by
  have hba := hd.band_le ha
  have hbb := hd.band_le hb
  rcases le_total a b with hab | hab
  · obtain ⟨t, rfl⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
    have e1 : Nat.dist a (a + t) = t := by unfold Nat.dist; omega
    rw [e1] at hm1
    have e2 : (t + 1) * s = t * s + s := by ring
    have e3 : (a + t) * s = a * s + t * s := by ring
    refine ⟨min (a * s) (n - m), ?_⟩
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, a = b + t := ⟨a - b, by omega⟩
    have e1 : Nat.dist (b + t) b = t := by unfold Nat.dist; omega
    rw [e1] at hm1
    have e2 : (t + 1) * s = t * s + s := by ring
    have e3 : (b + t) * s = b * s + t * s := by ring
    refine ⟨min (b * s) (n - m), ?_⟩
    omega

omit [NeZero n] in
theorem sqDist_lt (hd : HDims n k s) {E Z : Sq k} (hal : E.1 = Z.1 ∨ E.2 = Z.2) :
    sqDist E Z + 1 ≤ k := by
  have := E.1.isLt; have := E.2.isLt; have := Z.1.isLt; have := Z.2.isLt
  unfold sqDist Nat.dist
  rcases hal with h | h <;> rw [h] <;> omega

/-- A square box covering the squares `E` and `Z`. -/
theorem jump_box (hd : HDims n k s) {E Z : Sq k} (hal : E.1 = Z.1 ∨ E.2 = Z.2) :
    ∃ r0 c0, r0 + (sqDist E Z + 1) * s ≤ n ∧ c0 + (sqDist E Z + 1) * s ≤ n ∧
      ∀ Q : Sq k, (Q = E ∨ Q = Z) → ∀ x : Cell n, InBox (Q.1.val * s) (Q.2.val * s) s x →
        InBox r0 c0 ((sqDist E Z + 1) * s) x := by
  have hm2 : (sqDist E Z + 1) * s ≤ n := by
    rw [← hd.mul]; exact Nat.mul_le_mul_right s (sqDist_lt hd hal)
  have h1 : (Nat.dist E.1.val Z.1.val + 1) * s ≤ (sqDist E Z + 1) * s :=
    Nat.mul_le_mul_right s (by unfold sqDist; omega)
  have h2 : (Nat.dist E.2.val Z.2.val + 1) * s ≤ (sqDist E Z + 1) * s :=
    Nat.mul_le_mul_right s (by unfold sqDist; omega)
  obtain ⟨r0, a1, a2, a3, a4, a5⟩ := interval_cover hd E.1.isLt Z.1.isLt h1 hm2
  obtain ⟨c0, b1, b2, b3, b4, b5⟩ := interval_cover hd E.2.isLt Z.2.isLt h2 hm2
  refine ⟨r0, c0, a1, b1, ?_⟩
  rintro Q (rfl | rfl) x ⟨x1, x2, x3, x4⟩ <;> unfold InBox <;> omega

/-- The endpoints of a jump from `E` to `Z` and the jump itself. -/
theorem jump_ends (hd : HDims n k s) {E Z : Sq k} (hal : E.1 = Z.1 ∨ E.2 = Z.2) :
    ∃ e0 z : Cell n, reservoir k s E e0 ∧ reservoir k s Z z ∧
      z.1.val ≠ Z.1.val * s + (k + 2) ∧
      ∀ B' : Board n, blank B' = e0 →
        ∃ p : Path B' (swapCells B' (blank B') z), p.inefficientMoves ≤ 13 * (sqDist E Z * s + 2) := by
  have hks := hd.k_lt_s
  have hroom := hd.room
  have hE1 := hd.band_le E.1.isLt
  have hE2 := hd.band_le E.2.isLt
  have hZ1 := hd.band_le Z.1.isLt
  have hZ2 := hd.band_le Z.2.isLt
  let e0 : Cell n := mkCell n (E.1.val * s + k) (E.2.val * s + k)
  have e0f : e0.1.val = E.1.val * s + k := mkCell_fst (by omega)
  have e0s : e0.2.val = E.2.val * s + k := mkCell_snd (by omega)
  have he0 : reservoir k s E e0 := (reservoir_iff hd).mpr (by omega)
  rcases hal with h | h
  · have hs1 : E.1.val * s = Z.1.val * s := by rw [h]
    have hd0 : sqDist E Z = Nat.dist E.2.val Z.2.val := by
      unfold sqDist; rw [h, Nat.dist_self, zero_add]
    have hdm := Nat.dist_mul_right E.2.val s Z.2.val
    obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (E.2.val * s + Z.2.val * s + jp) % 2 = 1 :=
      ⟨if (E.2.val * s + Z.2.val * s) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
        by split_ifs <;> omega⟩
    let z : Cell n := mkCell n (Z.1.val * s + k) (Z.2.val * s + k + jp)
    have zf : z.1.val = Z.1.val * s + k := mkCell_fst (by omega)
    have zs : z.2.val = Z.2.val * s + k + jp := mkCell_snd (by omega)
    refine ⟨e0, z, he0, (reservoir_iff hd).mpr (by omega), by omega, fun B' hB' => ?_⟩
    obtain ⟨p, hp⟩ := exists_hjump_step hd.two_le_n B' z
      (by rw [hB', e0f, zf]; simp [Nat.dist]; omega) (by rw [hB', e0f, e0s, zf, zs]; omega)
    refine ⟨p, hp.trans ?_⟩
    rw [hB', e0s, zs, hd0]
    unfold Nat.dist at hdm ⊢
    omega
  · have hs2 : E.2.val * s = Z.2.val * s := by rw [h]
    have hd0 : sqDist E Z = Nat.dist E.1.val Z.1.val := by
      unfold sqDist; rw [h, Nat.dist_self, add_zero]
    have hdm := Nat.dist_mul_right E.1.val s Z.1.val
    obtain ⟨jp, hjp1, hjp2⟩ : ∃ jp, jp ≤ 1 ∧ (E.1.val * s + Z.1.val * s + jp) % 2 = 1 :=
      ⟨if (E.1.val * s + Z.1.val * s) % 2 = 1 then 0 else 1, by split_ifs <;> omega,
        by split_ifs <;> omega⟩
    let z : Cell n := mkCell n (Z.1.val * s + k + jp) (Z.2.val * s + k)
    have zf : z.1.val = Z.1.val * s + k + jp := mkCell_fst (by omega)
    have zs : z.2.val = Z.2.val * s + k := mkCell_snd (by omega)
    refine ⟨e0, z, he0, (reservoir_iff hd).mpr (by omega), by omega, fun B' hB' => ?_⟩
    obtain ⟨p, hp⟩ := exists_vjump_step hd.two_le_n B' z
      (by rw [hB', e0s, zs]; simp [Nat.dist]; omega) (by rw [hB', e0f, e0s, zf, zs]; omega)
    refine ⟨p, hp.trans ?_⟩
    rw [hB', e0f, zf, hd0]
    unfold Nat.dist at hdm ⊢
    omega

end SlidingPuzzle.Hub
