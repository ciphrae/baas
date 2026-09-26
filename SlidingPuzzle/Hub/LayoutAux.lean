import Mathlib

/-! # Arithmetic for the hub layout

Plain facts about `ℕ` used to decode board cells into regions and corridor
positions (`Hub/Layout.lean`). -/
namespace SlidingPuzzle.Hub.LayoutAux

theorem divmod {s b i : ℕ} (hi : i < s) : (b * s + i) / s = b ∧ (b * s + i) % s = i := by
  have hs : 0 < s := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem divmod_eq {s b i b' i' : ℕ} (hi : i < s) (hi' : i' < s)
    (h : b * s + i = b' * s + i') : b = b' ∧ i = i' := by
  have h1 := divmod (b := b) hi
  have h2 := divmod (b := b') hi'
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

theorem block_lt {k s b i : ℕ} (hb : b < k) (hi : i < s) : b * s + i < k * s := by
  have : (b + 1) * s ≤ k * s := Nat.mul_le_mul_right _ hb
  rw [Nat.succ_mul] at this
  omega

theorem sub_mul_add {k c s : ℕ} (h : c < k) : (k - 1 - c) * s + (c + 1) * s = k * s := by
  rw [← Nat.add_mul]; congr 1; omega

theorem div_lt_of_lt_mul' {q a m : ℕ} (h : q < a * m) : q / m < a :=
  Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)

theorem div_eq_bounds {x c s : ℕ} (hs : 0 < s) (h : x / s = c) : c * s ≤ x ∧ x < c * s + s := by
  subst h
  have := Nat.div_add_mod' x s
  have := Nat.mod_lt x hs
  omega

end SlidingPuzzle.Hub.LayoutAux
