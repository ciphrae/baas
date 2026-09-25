import SlidingPuzzle.Algorithm.Accounting
import SlidingPuzzle.Algorithm.Transport.Vertical
import SlidingPuzzle.Algorithm.Transport.Jumps

/-! A monotone schedule of vertical corridor bands. Only the first band may
contain inefficient ordinary slides; each crossing pays a short-jump budget. -/
namespace SlidingPuzzle.Partition
noncomputable section
open Classical

/-- Traverse successive good row intervals separated by bands of width L+U.
The threshold `cap` lies before the end of the starting block, so all later
ordinary slides are efficient. The result includes the actual legal path. -/
theorem exists_banded_vertical_route {n k : ℕ} [NeZero n]
    (hk : Dims n k) (hn : 2 ≤ n) (K L U : ℕ) (hsize : n = k*K)
    (hwidth : L+U+2 ≤ K) (i : GroupIndex k)
    (backwards : Bool) (column : Fin n) (cap : ℕ)
    (hefficient : ∀ (x y : Fin n) (t : Tile n), x.val+1 = y.val → cap ≤ x.val →
      t ∈ targetGroup i →
      gridDistance (corridorCell true backwards column x) (position (target n) t)+1 =
        gridDistance (corridorCell true backwards column y) (position (target n) t))
    (A : Board n)
    (hfamily : ∀ (r : Fin k) (x : Fin n), r.val*K+L ≤ x.val →
      x.val < (r.val+1)*K-U → A (corridorCell true backwards column x) ∈ targetGroup i)
    (s t : Fin k) (hst : s ≤ t) (a b : Fin n)
    (ha : a.val = s.val*K+L)
    (hb : t.val*K+L ≤ b.val ∧ b.val < (t.val+1)*K-U)
    (hcap : cap ≤ (s.val+1)*K)
    (B : Board n) (hAB : GroupEquivalent i A B)
    (hblank : blank B = corridorCell true backwards column a) :
    ∃ D : Board n, ∃ p : Path B D,
      blank D = corridorCell true backwards column b ∧ GroupEquivalent i A D ∧
      p.inefficientMoves ≤ cap-a.val + (t.val-s.val)*(26*(L+U+3)) ∧
      (s = t → p.inefficientMoves ≤ b.val-a.val) := by
  let line := corridorCell true backwards column
  have hinj : Function.Injective line := by
    intro x y h
    cases backwards <;> simpa [line, corridorCell] using h
  have hadj : ∀ x y : Fin n, x.val+1 = y.val → gridDistance (line x) (line y) = 1 := by
    intro x y h
    cases backwards <;> simp [line, corridorCell, gridDistance, Fin.rev, Nat.dist] <;> omega
  generalize hd : t.val-s.val = d
  induction d generalizing s a B with
  | zero =>
    have hst' : s = t := Fin.ext (by omega)
    subst s
    have hab : a ≤ b := by change a.val ≤ b.val; omega
    obtain ⟨D, p, hD, hBD, hp, hp'⟩ := exists_group_corridor_route hk i line hinj hadj cap
      hefficient a b hab B hblank (by
        intro x hax hxb hxa
        apply hAB.mem_targetGroup _ (by rw [hblank]; exact fun h => hxa (hinj h))
        exact hfamily t x (by change a.val ≤ x.val at hax; omega)
          (by change x.val ≤ b.val at hxb; omega))
    exact ⟨D, p, hD, hAB.trans hBD, by simpa using hp, fun _ => hp'⟩
  | succ d ih =>
    have hslt : s.val < t.val := by omega
    have hsbound : (s.val+1)*K ≤ n := by
      rw [hsize]
      exact Nat.mul_le_mul_right K s.isLt
    have hK : K ≤ (s.val+1)*K := by simp only [Nat.add_mul, Nat.one_mul]; omega
    let z : Fin n := ⟨(s.val+1)*K-U-1, by omega⟩
    have haz : a ≤ z := by
      change a.val ≤ (s.val+1)*K-U-1
      rw [ha]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    obtain ⟨C, p, hC, hBC, hp, -⟩ := exists_group_corridor_route hk i line hinj hadj cap
      hefficient a z haz B hblank (by
        intro x hax hxz hxa
        apply hAB.mem_targetGroup _ (by rw [hblank]; exact fun h => hxa (hinj h))
        apply hfamily s x
        · change a.val ≤ x.val at hax; omega
        · change x.val ≤ (s.val+1)*K-U-1 at hxz
          have : U+1 ≤ (s.val+1)*K := by omega
          omega)
    have hAC := hAB.trans hBC
    let s' : Fin k := ⟨s.val+1, by omega⟩
    have hs'bound : (s'.val+1)*K ≤ n := by
      rw [hsize]
      exact Nat.mul_le_mul_right K s'.isLt
    let a' : Fin n := ⟨s'.val*K+L, by
      have : L < K := by omega
      simp only [Nat.add_mul, Nat.one_mul] at hs'bound
      omega⟩
    let u : Fin n := ⟨z.val-1, by have := z.isLt; omega⟩
    have huz : u.val+1 = z.val := by dsimp [u, z]; omega
    have hzu : line u ≠ blank C := by
      rw [hC]
      exact fun h => (by have := congrArg Fin.val (hinj h); omega)
    have hza' : line a' ≠ blank C := by
      rw [hC]
      intro h
      have hv := congrArg Fin.val (hinj h)
      dsimp [a', s', z] at hv
      omega
    have htileU : C (line u) ∈ targetGroup i := by
      apply hAC.mem_targetGroup _ hzu
      apply hfamily s u
      · dsimp [u, z]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      · dsimp [u, z]
        have : U+2 ≤ (s.val+1)*K := by omega
        omega
    have htileA' : C (line a') ∈ targetGroup i := by
      apply hAC.mem_targetGroup _ hza'
      apply hfamily s' a' le_rfl
      dsimp [a']
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    obtain ⟨F, q, hF, hCF, hq⟩ := exists_group_vertical_jump hk hn C i (line a') (line u)
      htileA' htileU (by rw [hC]; simp [line, corridorCell])
      (by rw [hC, gridDistance_comm]; exact hadj u z huz)
    have hgap : Nat.dist (blank C).1.val (line a').1.val ≤ L+U+1 := by
      rw [hC]
      cases backwards <;> simp only [line, corridorCell, ↓reduceIte, Bool.false_eq_true,
        Fin.rev, Nat.dist] <;>
        dsimp [a', s', z] <;> omega
    have hq' : q.inefficientMoves ≤ 26*(L+U+3) :=
      q.inefficientMoves_le_length.trans (hq.trans (Nat.mul_le_mul_left 26 (by omega)))
    have hs't : s' ≤ t := by change s.val+1 ≤ t.val; omega
    have hcap' : cap ≤ (s'.val+1)*K := hcap.trans (Nat.mul_le_mul_right K (by
      dsimp [s']; omega))
    obtain ⟨D, v, hD, hAD, hv, -⟩ := ih s' hs't a' rfl hcap' F (hAC.trans hCF) hF (by
      dsimp [s']; omega)
    have hzero : cap-a'.val = 0 := by dsimp [a', s']; omega
    rw [hzero, Nat.zero_add] at hv
    refine ⟨D, p.append (q.append v), hD, hAD, ?_, fun h => absurd h (by
      intro h'; have := congrArg Fin.val h'; omega)⟩
    simp only [Path.inefficientMoves_append]
    calc
      _ ≤ (cap-a.val) + 26*(L+U+3) + d*(26*(L+U+3)) := by omega
      _ = _ := by ring

end
end SlidingPuzzle.Partition
