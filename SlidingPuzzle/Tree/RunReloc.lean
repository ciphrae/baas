import SlidingPuzzle.Tree.RunChain
import SlidingPuzzle.Hub.RoundWalk

/-! # Relocations of the blank

`hReloc G E Z` moves the blank from `E` to `Z` by one jump (aligned squares) or
two through the corner `(Z.1, E.2)`; each jump carries a free tile of its target
square back to its start. The jumps cost at most `3 (s + 3)` per unit of the
relocation weight of `RoundWalk`. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq sqDist HEvent relocWeight)

variable {k q : ℕ} (L : LaneSys k q)

/-- One jump carrying a free tile of `Z` to `E`. -/
noncomputable def hLeg (s : ℕ) (G : GS k q) (E Z : Sq k) : GS k q := gJump s G E Z (pickFree G Z)

/-- A relocation. -/
noncomputable def hReloc (s : ℕ) (G : GS k q) (E Z : Sq k) : GS k q :=
  if E.1 = Z.1 ∨ E.2 = Z.2 then hLeg s G E Z else hLeg s (hLeg s G E (Z.1, E.2)) (Z.1, E.2) Z

section legs

variable {s : ℕ} {σ0 : IState k q} {F0 : ℕ}

theorem hLeg_same (G : GS k q) (E Z : Sq k) :
    (hLeg s G E Z).ins = G.ins ∧ (hLeg s G E Z).sched = G.sched ∧
      (hLeg s G E Z).stock = G.stock ∧ (hLeg s G E Z).B = G.B ∧ (hLeg s G E Z).dA = G.dA ∧
      (hLeg s G E Z).served = G.served ∧ (hLeg s G E Z).sent = G.sent ∧
      (hLeg s G E Z).nh = G.nh ∧ (hLeg s G E Z).wt = G.wt ∧
      (hLeg s G E Z).σ.lane = G.σ.lane ∧ (hLeg s G E Z).σ.blank = Z :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hLeg_fr (G : GS k q) (E Z : Sq k) (hEZ : E ≠ Z) (hf : 1 ≤ fr G Z) (Q : Sq k) :
    fr (hLeg s G E Z) Q + (if Q = Z then 1 else 0) = fr G Q + (if Q = E then 1 else 0) := by
  have hp := pickFree_spec G Z hf
  unfold fr hLeg gJump
  simp only
  have h := sum_sum_sub_add (fun Q' y => if Q' = Q then G.free Q' y else 0) True True
    Z (pickFree G Z) E (pickFree G Z)
  have e : ∀ y, (G.free Q y - (if Q = Z ∧ y = pickFree G Z then 1 else 0) +
      (if Q = E ∧ y = pickFree G Z then 1 else 0)) + (if Q = Z ∧ y = pickFree G Z then 1 else 0) =
      G.free Q y + (if Q = E ∧ y = pickFree G Z then 1 else 0) := by
    intro y
    split_ifs with h1 h2 h2 <;> try omega
    · obtain ⟨rfl, rfl⟩ := h1; omega
    · obtain ⟨rfl, rfl⟩ := h1; omega
  have e1 := Finset.sum_congr rfl fun y (_ : y ∈ univ) => e y
  simp only [sum_add_distrib] at e1 ⊢
  have hZ : ∑ y, (if Q = Z ∧ y = pickFree G Z then 1 else 0) = if Q = Z then 1 else 0 := by
    by_cases hq : Q = Z
    · simp [hq]
    · simp [hq]
  have hE : ∑ y, (if Q = E ∧ y = pickFree G Z then 1 else 0) = if Q = E then 1 else 0 := by
    by_cases hq : Q = E
    · simp [hq]
    · simp [hq]
  rw [hZ, hE] at e1
  rw [hE]
  omega

theorem hLeg_linv {G : GS k q} (hL : LInv L s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hal : E.1 = Z.1 ∨ E.2 = Z.2) (hf : 1 ≤ fr G Z) :
    LInv L s σ0 F0 (hLeg s G E Z) :=
  gJump_linv L hL hb hEZ hal (pickFree_spec G Z hf)

theorem hLeg_jc (G : GS k q) (E Z : Sq k) :
    (hLeg s G E Z).jc = G.jc + (s + 3) * (13 + 21 * sqDist E Z) := rfl

end legs

theorem corner_facts {E Z : Sq k} (c : ¬ (E.1 = Z.1 ∨ E.2 = Z.2)) :
    E ≠ (Z.1, E.2) ∧ (Z.1, E.2) ≠ Z ∧ (E.1 = (Z.1, E.2).1 ∨ E.2 = (Z.1, E.2).2) ∧
      ((Z.1, E.2).1 = Z.1 ∨ (Z.1, E.2).2 = Z.2) ∧
      sqDist E (Z.1, E.2) + sqDist (Z.1, E.2) Z = sqDist E Z ∧ Z ≠ E := by
  push Not at c
  refine ⟨fun e => c.1 (by have := congrArg Prod.fst e; simpa using this),
    fun e => c.2 (by have := congrArg Prod.snd e; simpa using this), Or.inr rfl,
    Or.inl rfl, ?_, fun e => c.1 (by have := congrArg Prod.fst e; simpa using this.symm)⟩
  unfold sqDist; simp [Nat.dist_self]

section reloc

variable {s : ℕ} {σ0 : IState k q} {F0 : ℕ}

theorem hReloc_same (G : GS k q) (E Z : Sq k) :
    (hReloc s G E Z).ins = G.ins ∧ (hReloc s G E Z).sched = G.sched ∧
      (hReloc s G E Z).stock = G.stock ∧ (hReloc s G E Z).B = G.B ∧ (hReloc s G E Z).dA = G.dA ∧
      (hReloc s G E Z).served = G.served ∧ (hReloc s G E Z).sent = G.sent ∧
      (hReloc s G E Z).nh = G.nh ∧ (hReloc s G E Z).wt = G.wt ∧
      (hReloc s G E Z).σ.lane = G.σ.lane ∧ (hReloc s G E Z).σ.blank = Z := by
  unfold hReloc; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hReloc_linv {G : GS k q} (hL : LInv L s σ0 F0 G) {E Z : Sq k} (hb : G.σ.blank = E)
    (hEZ : E ≠ Z) (hf : ∀ Q, Q ≠ E → 1 ≤ fr G Q) :
    LInv L s σ0 F0 (hReloc s G E Z) ∧ (∀ Q, fr (hReloc s G E Z) Q + (if Q = Z then 1 else 0) =
      fr G Q + (if Q = E then 1 else 0)) ∧
      (hReloc s G E Z).jc ≤ G.jc + 3 * (s + 3) * relocWeight (HEvent.reloc E Z) := by
  unfold hReloc relocWeight
  split_ifs with c
  · refine ⟨hLeg_linv L hL hb hEZ c (hf Z (Ne.symm hEZ)), hLeg_fr G E Z hEZ (hf Z (Ne.symm hEZ)),
      ?_⟩
    rw [hLeg_jc]
    simp only [if_pos c]
    have : (s + 3) * (13 + 21 * sqDist E Z) ≤ 3 * (s + 3) * (16 + 7 * sqDist E Z) := by
      have := Nat.mul_le_mul_left (s + 3) (show 13 + 21 * sqDist E Z ≤ 3 * (16 + 7 * sqDist E Z)
        by omega)
      linarith
    omega
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := corner_facts c
    set C : Sq k := (Z.1, E.2)
    have hfC := hf C (Ne.symm h1)
    have L1 := hLeg_linv L hL hb h1 h3 hfC
    have f1 := hLeg_fr (s := s) G E C h1 hfC
    have hZ1 : 1 ≤ fr (hLeg s G E C) Z := by
      have := f1 Z; have := hf Z h6
      simp only [if_neg (Ne.symm h2), if_neg h6] at *; omega
    refine ⟨hLeg_linv L L1 rfl h2 h4 hZ1, ?_, ?_⟩
    · intro Q
      have g1 := f1 Q
      have g2 := hLeg_fr (s := s) (hLeg s G E C) C Z h2 hZ1 Q
      omega
    · rw [hLeg_jc, hLeg_jc]
      simp only [if_neg c]
      have : (s + 3) * (13 + 21 * sqDist E C) + (s + 3) * (13 + 21 * sqDist C Z) ≤
          3 * (s + 3) * (32 + 7 * sqDist E Z) := by
        rw [← mul_add]
        have := Nat.mul_le_mul_left (s + 3) (show 13 + 21 * sqDist E C + (13 + 21 * sqDist C Z)
          ≤ 3 * (32 + 7 * sqDist E Z) by omega)
        linarith
      omega

end reloc

end SlidingPuzzle.Tree
