import SlidingPuzzle.Tree.LaneSys

/-! # The `b`-ary hierarchy of lanes

`k = b^h` blocks, `q = h*b` offsets `o ↔ (ℓ, i)` (`finProdFinEquiv`). At level
`ℓ` a parent has `b*m` blocks, `m = b^(h-ℓ-1)`; offset `(ℓ, i)` carries, inside
each parent, the piece left of child `i` (landing at the child's first block)
and the piece right of it (landing at its last block). A hop goes to the near
end of the child containing the target at the first level where the two blocks
lie in different children. -/
namespace SlidingPuzzle.Tree

namespace Hier

open Finset

/-! ## Arithmetic of one level -/

section arith

variable {b m : ℕ}

theorem div_eq_of_bounds {M B x : ℕ} (h1 : B * M ≤ x) (h2 : x < B * M + M) : x / M = B :=
  Nat.div_eq_of_lt_le h1 (by rw [add_mul, one_mul]; exact h2)

/-- A block in the right piece of the child `i` (landing `t`, `t % (b m) = i m + m - 1`). -/
theorem right_piece {i t J : ℕ} (hm : 0 < m) (hi : i < b)
    (ht : t % (b * m) = i * m + (m - 1)) (h1 : t < J) (h2 : J ≤ t + (b - 1 - i) * m) :
    J / (b * m) = t / (b * m) ∧ i * m + (m - 1) < J % (b * m) := by
  have hM : 0 < b * m := Nat.mul_pos (by omega) hm
  have e := Nat.div_add_mod t (b * m)
  have e2 := Nat.div_add_mod J (b * m)
  have hbm : (b - 1 - i) * m + (i * m + (m - 1)) = b * m - 1 := by
    have : (b - 1 - i) + i + 1 = b := by omega
    have h3 : ((b - 1 - i) + i + 1) * m = b * m := by rw [this]
    rw [add_mul, add_mul, one_mul] at h3
    omega
  have hJ : J / (b * m) = t / (b * m) := by
    apply div_eq_of_bounds
    · rw [mul_comm]; omega
    · rw [mul_comm]; omega
  refine ⟨hJ, ?_⟩
  rw [hJ] at e2
  omega

/-- A block in the left piece of the child `i` (landing `t`, `t % (b m) = i m`). -/
theorem left_piece {i t J : ℕ} (hm : 0 < m)
    (ht : t % (b * m) = i * m) (h1 : J < t) (h2 : t ≤ J + i * m) (hb : 0 < b) :
    J / (b * m) = t / (b * m) ∧ J % (b * m) < i * m := by
  have hM : 0 < b * m := Nat.mul_pos hb hm
  have e := Nat.div_add_mod t (b * m)
  have e2 := Nat.div_add_mod J (b * m)
  have hlt := Nat.mod_lt t hM
  have hJ : J / (b * m) = t / (b * m) := by
    apply div_eq_of_bounds
    · rw [mul_comm]; omega
    · rw [mul_comm]; omega
  refine ⟨hJ, ?_⟩
  rw [hJ] at e2
  omega

theorem mul_mod_mul (x : ℕ) : (x * m) % (b * m) = (x % b) * m :=
  Nat.mul_mod_mul_right m x b

theorem mod_lt_mul {i : ℕ} (hi : i < b) (hm : 0 < m) : i * m + (m - 1) < b * m := by
  have : (i + 1) * m ≤ b * m := Nat.mul_le_mul_right m hi
  rw [add_mul, one_mul] at this
  omega

end arith

variable (b h : ℕ)

/-- Level of an offset. -/
def lev (o : Fin (h * b)) : ℕ := (finProdFinEquiv.symm o).1.val

/-- Child index of an offset. -/
def chi (o : Fin (h * b)) : ℕ := (finProdFinEquiv.symm o).2.val

/-- Child size at the level of an offset. -/
def csz (o : Fin (h * b)) : ℕ := b ^ (h - lev b h o - 1)

theorem lev_lt (o : Fin (h * b)) : lev b h o < h := (finProdFinEquiv.symm o).1.isLt

theorem chi_lt (o : Fin (h * b)) : chi b h o < b := (finProdFinEquiv.symm o).2.isLt

/-- Piece lengths. -/
def len (o : Fin (h * b)) (t : Fin (b ^ h)) (side : Bool) : ℕ :=
  if side then
    (if t.val % (b * csz b h o) = chi b h o * csz b h o + (csz b h o - 1) then
      (b - 1 - chi b h o) * csz b h o else 0)
  else
    (if t.val % (b * csz b h o) = chi b h o * csz b h o then chi b h o * csz b h o else 0)

/-- Target blocks routed through a piece: the blocks of the child. -/
def X (o : Fin (h * b)) (t : Fin (b ^ h)) (side : Bool) : Finset (Fin (b ^ h)) :=
  if len b h o t side = 0 then ∅ else univ.filter fun c => c.val / csz b h o = t.val / csz b h o

/-- `J` and `c` lie in different children at level `ℓ`. -/
def Sep (J c : ℕ) (ℓ : ℕ) : Prop := ℓ < h ∧ J / b ^ (h - ℓ - 1) ≠ c / b ^ (h - ℓ - 1)

instance (J c ℓ : ℕ) : Decidable (Sep b h J c ℓ) := by unfold Sep; infer_instance

theorem sep_exists {J c : ℕ} (hh : 0 < h) (hne : J ≠ c) : ∃ ℓ, Sep b h J c ℓ :=
  ⟨h - 1, by omega, by rw [show h - (h - 1) - 1 = 0 by omega]; simpa using hne⟩

open Classical in
/-- The level of a hop (`0` if `J = c`). -/
noncomputable def lvl (J c : Fin (b ^ h)) : ℕ :=
  if hx : ∃ ℓ, Sep b h J.val c.val ℓ then Nat.find hx else 0

open Classical in
/-- The hop from `J` toward `c`. -/
noncomputable def hop (hb : 2 ≤ b) (hh : 0 < h) (J c : Fin (b ^ h)) : Fin (h * b) × Fin (b ^ h) :=
  if hx : ∃ ℓ, Sep b h J.val c.val ℓ then
    let ℓ := Nat.find hx
    let m := b ^ (h - ℓ - 1)
    have hℓ : ℓ < h := (Nat.find_spec hx).1
    have hm : 0 < m := by positivity
    have hk : c.val / m * m + (m - 1) < b ^ h := by
      have e : b ^ h = b ^ (h - ℓ - 1) * b ^ (ℓ + 1) := by
        rw [← pow_add]; congr 1; omega
      have h1 : c.val < b ^ (h - ℓ - 1) * b ^ (ℓ + 1) := e ▸ c.isLt
      have h2 : c.val / m < b ^ (ℓ + 1) := Nat.div_lt_of_lt_mul h1
      have h3 : (c.val / m + 1) * m ≤ b ^ (ℓ + 1) * m := Nat.mul_le_mul_right m h2
      rw [add_mul, one_mul] at h3
      have : b ^ (ℓ + 1) * m = b ^ h := by rw [e, mul_comm]
      omega
    (finProdFinEquiv (⟨ℓ, hℓ⟩, ⟨(c.val / m) % b, Nat.mod_lt _ (by omega)⟩),
      ⟨if J.val < c.val then c.val / m * m else c.val / m * m + (m - 1), by
        split_ifs <;> omega⟩)
  else (⟨0, Nat.mul_pos hh (by omega)⟩, J)


/-! ## The hop in coordinates -/

section spec

variable {b h} (hb : 2 ≤ b) (hh : 0 < h)
include hh

theorem sep_of_ne {J c : Fin (b ^ h)} (hne : J ≠ c) : ∃ ℓ, Sep b h J.val c.val ℓ :=
  sep_exists b h hh (fun e => hne (Fin.ext e))

/-- Everything about the hop from `J` toward `c ≠ J`. -/
theorem hop_spec {J c : Fin (b ^ h)} (hne : J ≠ c) :
    ∃ ℓ i, ℓ < h ∧ i < b ∧ lvl b h J c = ℓ ∧
      lev b h (hop b h hb hh J c).1 = ℓ ∧ chi b h (hop b h hb hh J c).1 = i ∧
      csz b h (hop b h hb hh J c).1 = b ^ (h - ℓ - 1) ∧
      i = (c.val / b ^ (h - ℓ - 1)) % b ∧
      (hop b h hb hh J c).2.val = (if J.val < c.val then c.val / b ^ (h - ℓ - 1) * b ^ (h - ℓ - 1)
        else c.val / b ^ (h - ℓ - 1) * b ^ (h - ℓ - 1) + (b ^ (h - ℓ - 1) - 1)) ∧
      J.val / b ^ (h - ℓ - 1) ≠ c.val / b ^ (h - ℓ - 1) ∧
      J.val / (b * b ^ (h - ℓ - 1)) = c.val / (b * b ^ (h - ℓ - 1)) ∧
      (∀ ℓ' < ℓ, ¬ Sep b h J.val c.val ℓ') := by
  classical
  have hx := sep_of_ne hh hne
  set ℓ := Nat.find hx with hℓdef
  have hsp := Nat.find_spec hx
  have hmin : ∀ ℓ' < ℓ, ¬ Sep b h J.val c.val ℓ' := fun ℓ' h' => Nat.find_min hx h'
  have hℓ : ℓ < h := hsp.1
  refine ⟨ℓ, (c.val / b ^ (h - ℓ - 1)) % b, hℓ, Nat.mod_lt _ (by omega), ?_, ?_, ?_, ?_, rfl,
    ?_, hsp.2, ?_, hmin⟩
  · unfold lvl; rw [dif_pos hx]
  · unfold hop lev; rw [dif_pos hx]; simp [ℓ]
  · unfold hop chi; rw [dif_pos hx]; simp [ℓ]
  · unfold hop csz lev; rw [dif_pos hx]; simp [ℓ]
  · unfold hop; rw [dif_pos hx]
  · -- same parent
    have e : b * b ^ (h - ℓ - 1) = b ^ (h - ℓ) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · rw [h0, Nat.sub_zero, Nat.div_eq_of_lt J.isLt, Nat.div_eq_of_lt c.isLt]
    · have := hmin (ℓ - 1) (by omega)
      unfold Sep at this
      push Not at this
      have e2 : h - (ℓ - 1) - 1 = h - ℓ := by omega
      rw [e2] at this
      exact this (by omega)

end spec


/-! ## Pieces -/

section pieces

variable {b h}

theorem csz_pos (hb : 2 ≤ b) (o : Fin (h * b)) : 0 < csz b h o := by
  unfold csz; positivity

/-- The parent size divides `b^h`. -/
theorem parent_pow (o : Fin (h * b)) : b * csz b h o * b ^ lev b h o = b ^ h := by
  unfold csz
  have := lev_lt b h o
  rw [← pow_succ', ← pow_add]; congr 1; omega

theorem parent_le (hb : 2 ≤ b) (o : Fin (h * b)) : b * csz b h o ≤ b ^ h := by
  rw [← parent_pow o]
  exact Nat.le_mul_of_pos_right _ (by positivity)

/-- A block in a piece: same parent as the landing block, and on the correct side
of the child. -/
theorem inPiece_spec (hb : 2 ≤ b) {o : Fin (h * b)} {t : Fin (b ^ h)} {side : Bool} {J : ℕ}
    (hJ : InPiece (len b h o t side) t.val side J) :
    J / (b * csz b h o) = t.val / (b * csz b h o) ∧
      t.val % (b * csz b h o) = (if side then chi b h o * csz b h o + (csz b h o - 1)
        else chi b h o * csz b h o) ∧
      (if side then chi b h o * csz b h o + (csz b h o - 1) < J % (b * csz b h o)
        else J % (b * csz b h o) < chi b h o * csz b h o) := by
  have hm := csz_pos hb o
  have hi := chi_lt b h o
  cases side
  · simp only [len, Bool.false_eq_true, if_false] at hJ ⊢
    split_ifs at hJ with ht
    · obtain ⟨h1, h2⟩ := left_piece hm ht hJ.1 hJ.2 (by omega)
      exact ⟨h1, ht, h2⟩
    · unfold InPiece at hJ; simp at hJ; omega
  · simp only [len, if_true] at hJ ⊢
    split_ifs at hJ with ht
    · obtain ⟨h1, h2⟩ := right_piece hm hi ht hJ.1 hJ.2
      exact ⟨h1, ht, h2⟩
    · unfold InPiece at hJ; simp at hJ; omega

theorem right_lt (hb : 2 ≤ b) (o : Fin (h * b)) (t : Fin (b ^ h)) :
    t.val + len b h o t true < b ^ h := by
  have hm := csz_pos hb o
  have hi := chi_lt b h o
  simp only [len, if_true]
  split_ifs with ht
  · have hM : 0 < b * csz b h o := Nat.mul_pos (by omega) hm
    have e := Nat.div_add_mod t.val (b * csz b h o)
    have hpar := parent_pow (b := b) (h := h) o
    have h1 : t.val / (b * csz b h o) < b ^ lev b h o := by
      apply Nat.div_lt_of_lt_mul; rw [hpar]; exact t.isLt
    have h2 : b * csz b h o * (t.val / (b * csz b h o) + 1) ≤ b * csz b h o * b ^ lev b h o :=
      Nat.mul_le_mul_left _ h1
    rw [hpar, mul_add, mul_one] at h2
    have hbm : (b - 1 - chi b h o) * csz b h o + (chi b h o * csz b h o + (csz b h o - 1)) =
        b * csz b h o - 1 := by
      have : (b - 1 - chi b h o) + chi b h o + 1 = b := by omega
      have h3 : ((b - 1 - chi b h o) + chi b h o + 1) * csz b h o = b * csz b h o := by rw [this]
      rw [add_mul, add_mul, one_mul] at h3
      omega
    omega
  · simp only [add_zero]; exact t.isLt

theorem left_le (o : Fin (h * b)) (t : Fin (b ^ h)) : len b h o t false ≤ t.val := by
  simp only [len, Bool.false_eq_true, if_false]
  split_ifs with ht
  · rw [← ht]; exact Nat.mod_le _ _
  · exact Nat.zero_le _

theorem disj (hb : 2 ≤ b) (o : Fin (h * b)) (t t' : Fin (b ^ h)) (side side' : Bool) (J : ℕ)
    (h1 : InPiece (len b h o t side) t side J) (h2 : InPiece (len b h o t' side') t' side' J) :
    t = t' ∧ side = side' := by
  obtain ⟨a1, a2, a3⟩ := inPiece_spec hb h1
  obtain ⟨b1, b2, b3⟩ := inPiece_spec hb h2
  have key : t.val / (b * csz b h o) = t'.val / (b * csz b h o) := a1.symm.trans b1
  have fin : t.val % (b * csz b h o) = t'.val % (b * csz b h o) → t = t' := fun hmod =>
    Fin.ext (by rw [← Nat.div_add_mod t.val (b * csz b h o),
      ← Nat.div_add_mod t'.val (b * csz b h o), key, hmod])
  cases side <;> cases side'
  · exact ⟨fin (by simpa using a2.trans b2.symm), rfl⟩
  · simp only [Bool.false_eq_true, if_false, if_true] at a3 b3; omega
  · simp only [Bool.false_eq_true, if_false, if_true] at a3 b3; omega
  · exact ⟨fin (by simpa using a2.trans b2.symm), rfl⟩

theorem avoid (hb : 2 ≤ b) (o : Fin (h * b)) (t t' : Fin (b ^ h)) (side side' : Bool)
    (hpos : 0 < len b h o t side) : ¬ InPiece (len b h o t' side') t' side' t.val := by
  intro hin
  obtain ⟨-, -, a3⟩ := inPiece_spec hb hin
  have hm := csz_pos hb o
  have ht : t.val % (b * csz b h o) = (if side then chi b h o * csz b h o + (csz b h o - 1)
      else chi b h o * csz b h o) := by
    cases side <;> simp only [len, Bool.false_eq_true, if_false, if_true] at hpos ⊢ <;>
      split_ifs at hpos with hh <;> first | exact hh | omega
  cases side <;> cases side' <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> omega

end pieces
/-! ## Hops -/

section hops

variable {b h} (hb : 2 ≤ b) (hh : 0 < h)
include hb hh

/-- The landing block of a hop, as a multiple of the child size. -/
theorem hop_land {J c : Fin (b ^ h)} (hne : J ≠ c) :
    ∃ ℓ i A P, ℓ < h ∧ i < b ∧ lvl b h J c = ℓ ∧
      lev b h (hop b h hb hh J c).1 = ℓ ∧ chi b h (hop b h hb hh J c).1 = i ∧
      csz b h (hop b h hb hh J c).1 = b ^ (h - ℓ - 1) ∧
      c.val / b ^ (h - ℓ - 1) = A ∧ A = P * b + i ∧
      c.val / (b * b ^ (h - ℓ - 1)) = P ∧ J.val / (b * b ^ (h - ℓ - 1)) = P ∧
      J.val / b ^ (h - ℓ - 1) ≠ A ∧
      (hop b h hb hh J c).2.val = (if J.val < c.val then A * b ^ (h - ℓ - 1)
        else A * b ^ (h - ℓ - 1) + (b ^ (h - ℓ - 1) - 1)) ∧
      (∀ ℓ' < ℓ, ¬ Sep b h J.val c.val ℓ') := by
  obtain ⟨ℓ, i, hℓ, hi, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hop_spec hb hh hne
  refine ⟨ℓ, i, c.val / b ^ (h - ℓ - 1), c.val / (b * b ^ (h - ℓ - 1)), hℓ, hi, e1, e2, e3, e4,
    rfl, ?_, rfl, e8.trans rfl, e7, e6, e9⟩
  rw [e5, Nat.mul_comm b, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ b).symm

theorem hop_in (J c : Fin (b ^ h)) (hne : J ≠ c) :
    InPiece (len b h (hop b h hb hh J c).1 (hop b h hb hh J c).2 (decide (c < J)))
      (hop b h hb hh J c).2 (decide (c < J)) J.val := by
  obtain ⟨ℓ, i, A, P, hℓ, hi, -, -, e3, e4, eA, eAP, eP, eJ, hJA, et, -⟩ := hop_land hb hh hne
  set m := b ^ (h - ℓ - 1) with hm_def
  have hm : 0 < m := by positivity
  have hPM : A * m = P * (b * m) + i * m := by rw [eAP]; ring
  have ec := Nat.div_add_mod c.val m
  have ecl := Nat.mod_lt c.val hm
  have eJ2 := Nat.div_add_mod J.val (b * m)
  have eJl := Nat.mod_lt J.val (Nat.mul_pos (by omega : 0 < b) hm)
  have eJm := Nat.div_add_mod J.val m
  have eJml := Nat.mod_lt J.val hm
  rw [eP] at *
  rw [eJ] at eJ2
  have him : i * m + (m - 1) < b * m := mod_lt_mul hi hm
  rcases lt_or_gt_of_ne (show J.val ≠ c.val from fun e => hne (Fin.ext e)) with hlt | hlt
  · have hd : decide (c < J) = false := by simp; exact hlt.le
    rw [hd]
    have hle : J.val / m ≤ A := eA ▸ Nat.div_le_div_right hlt.le
    have hlt2 : J.val / m + 1 ≤ A := by omega
    have h3 : (J.val / m + 1) * m ≤ A * m := Nat.mul_le_mul_right m hlt2
    rw [add_mul, one_mul] at h3
    have htv : (hop b h hb hh J c).2.val = A * m := by rw [et, if_pos hlt]
    have hmod : (hop b h hb hh J c).2.val % (b * m) = i * m := by
      rw [htv, hPM, mul_comm P, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    unfold InPiece len
    simp only [Bool.false_eq_true, if_false]
    rw [e3, e4, hmod, if_pos rfl]
    rw [mul_comm m (J.val / m)] at eJm
    rw [mul_comm (b * m)] at eJ2
    constructor <;> omega
  · have hd : decide (c < J) = true := by simp; exact hlt
    rw [hd]
    have hle : A ≤ J.val / m := eA ▸ Nat.div_le_div_right hlt.le
    have hlt2 : A + 1 ≤ J.val / m := by omega
    have h3 : (A + 1) * m ≤ J.val / m * m := Nat.mul_le_mul_right m hlt2
    rw [add_mul, one_mul] at h3
    have htv : (hop b h hb hh J c).2.val = A * m + (m - 1) := by
      rw [et, if_neg (by omega)]
    have hmod : (hop b h hb hh J c).2.val % (b * m) = i * m + (m - 1) := by
      rw [htv, hPM, mul_comm P, add_assoc, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    unfold InPiece len
    simp only [if_true]
    rw [e3, e4, hmod, if_pos rfl]
    rw [mul_comm m (J.val / m)] at eJm
    rw [mul_comm (b * m)] at eJ2
    have hbm : (b - 1 - i) * m + (i * m + (m - 1)) = b * m - 1 := by
      have : (b - 1 - i) + i + 1 = b := by omega
      have h4 : ((b - 1 - i) + i + 1) * m = b * m := by rw [this]
      rw [add_mul, add_mul, one_mul] at h4
      omega
    constructor <;> omega

theorem hop_le (J c : Fin (b ^ h)) (hlt : J < c) : (hop b h hb hh J c).2 ≤ c := by
  obtain ⟨ℓ, i, A, P, -, -, -, -, -, -, eA, -, -, -, -, et, -⟩ := hop_land hb hh (ne_of_lt hlt)
  show (hop b h hb hh J c).2.val ≤ c.val
  rw [et, if_pos (show J.val < c.val from hlt), ← eA]
  exact Nat.div_mul_le_self _ _

theorem hop_ge (J c : Fin (b ^ h)) (hlt : c < J) : c ≤ (hop b h hb hh J c).2 := by
  obtain ⟨ℓ, i, A, P, -, -, -, -, -, -, eA, -, -, -, -, et, -⟩ := hop_land hb hh (ne_of_gt hlt)
  show c.val ≤ (hop b h hb hh J c).2.val
  have hm : 0 < b ^ (h - ℓ - 1) := by positivity
  have := Nat.div_add_mod c.val (b ^ (h - ℓ - 1))
  have := Nat.mod_lt c.val hm
  rw [et, if_neg (by have : c.val < J.val := hlt; omega), ← eA, mul_comm]
  omega

/-- The landing block lies in the target's child. -/
theorem hop_child {J c : Fin (b ^ h)} (hne : J ≠ c) :
    (hop b h hb hh J c).2.val / csz b h (hop b h hb hh J c).1 =
      c.val / csz b h (hop b h hb hh J c).1 := by
  obtain ⟨ℓ, i, A, P, -, -, -, -, -, e4, eA, -, -, -, -, et, -⟩ := hop_land hb hh hne
  have hm : 0 < b ^ (h - ℓ - 1) := by positivity
  rw [e4, eA, et]
  split_ifs
  · exact Nat.mul_div_cancel _ hm
  · apply div_eq_of_bounds <;> omega

theorem hop_X (J c : Fin (b ^ h)) (hne : J ≠ c) :
    c ∈ X b h (hop b h hb hh J c).1 (hop b h hb hh J c).2 (decide (c < J)) := by
  have hin := hop_in hb hh J c hne
  unfold X
  rw [if_neg]
  · simp only [mem_filter, mem_univ, true_and]
    exact (hop_child hb hh hne).symm
  · intro h0
    rw [h0] at hin
    unfold InPiece at hin
    split at hin <;> omega

theorem lvl_lt (J c : Fin (b ^ h)) (hne : J ≠ c) : lvl b h J c < h := by
  obtain ⟨ℓ, -, hℓ, -, e1, -⟩ := hop_spec hb hh hne
  rw [e1]; exact hℓ

theorem lvl_hop (J c : Fin (b ^ h)) (hne : J ≠ c) (ht : (hop b h hb hh J c).2 ≠ c) :
    lvl b h J c < lvl b h (hop b h hb hh J c).2 c := by
  have hch := hop_child hb hh hne
  obtain ⟨ℓ, -, -, -, e1, e2, -, e4, -⟩ := hop_spec hb hh hne
  obtain ⟨ℓ2, -, -, -, f1, -, -, -, -, -, f7, -⟩ := hop_spec hb hh ht
  rw [e1, f1]
  by_contra hle
  push Not at hle
  rw [e4] at hch
  apply f7
  have e : b ^ (h - ℓ2 - 1) = b ^ (h - ℓ - 1) * b ^ (ℓ - ℓ2) := by
    rw [← pow_add]; congr 1
    have := lev_lt b h (hop b h hb hh J c).1
    omega
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hch]

end hops
/-! ## Sums at a landing block -/

section sums

variable {b h}

theorem sum_le_of_unique {ι : Type*} [Fintype ι] (f : ι → ℕ) (P : ι → Prop) [DecidablePred P]
    (K : ℕ) (hP : ∀ i j, P i → P j → i = j) (hf : ∀ i, f i ≤ if P i then K else 0) :
    ∑ i, f i ≤ K := by
  calc ∑ i, f i ≤ ∑ i, (if P i then K else 0) := sum_le_sum fun i _ => hf i
    _ = (univ.filter P).card * K := by rw [← sum_filter, sum_const, smul_eq_mul]
    _ ≤ 1 * K := Nat.mul_le_mul_right K (card_le_one.mpr fun i hi j hj =>
        hP i j (mem_filter.mp hi).2 (mem_filter.mp hj).2)
    _ = K := one_mul K

theorem lev_mk (ℓ : Fin h) (i : Fin b) : lev b h (finProdFinEquiv (ℓ, i)) = ℓ.val := by
  simp [lev]

theorem chi_mk (ℓ : Fin h) (i : Fin b) : chi b h (finProdFinEquiv (ℓ, i)) = i.val := by
  simp [chi]

/-- Per level and side, at most one child has a nonempty piece landing at `t`. -/
theorem level_sum (hb : 2 ≤ b) (t : Fin (b ^ h)) (ℓ : Fin h) (side : Bool)
    (f : Fin (h * b) → ℕ)
    (hf : ∀ o, f o ≤ if len b h o t side = 0 then 0 else b ^ h) :
    ∑ i : Fin b, f (finProdFinEquiv (ℓ, i)) ≤ b ^ h := by
  set m := b ^ (h - ℓ.val - 1)
  have hm : 0 < m := by positivity
  have hcsz : ∀ i : Fin b, csz b h (finProdFinEquiv (ℓ, i)) = m := by
    intro i; simp only [csz, lev_mk]; rfl
  apply sum_le_of_unique _ (fun i : Fin b => t.val % (b * m) =
    (if side then i.val * m + (m - 1) else i.val * m)) (b ^ h)
  · intro i j hi hj
    apply Fin.ext
    have e := hi.symm.trans hj
    have := Nat.eq_of_mul_eq_mul_right hm (show i.val * m = j.val * m by split_ifs at e <;> omega)
    exact this
  · intro i
    refine (hf _).trans ?_
    by_cases hl : len b h (finProdFinEquiv (ℓ, i)) t side = 0
    · rw [if_pos hl]; exact Nat.zero_le _
    · rw [if_neg hl, if_pos]
      simp only [len, chi_mk, hcsz] at hl
      cases side <;> simp only [Bool.false_eq_true, if_false, if_true] at hl ⊢ <;>
        split_ifs at hl with hc <;> first | exact hc | exact absurd rfl hl

theorem sum_side_le (hb : 2 ≤ b) (t : Fin (b ^ h)) (f : Fin (h * b) → Bool → ℕ)
    (hf : ∀ o side, f o side ≤ if len b h o t side = 0 then 0 else b ^ h) :
    ∑ o, ∑ side, f o side ≤ 2 * h * b ^ h := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  calc ∑ ℓ : Fin h, ∑ i : Fin b, ∑ side, f (finProdFinEquiv (ℓ, i)) side
      = ∑ ℓ : Fin h, ∑ side, ∑ i : Fin b, f (finProdFinEquiv (ℓ, i)) side := by
        refine sum_congr rfl fun ℓ _ => sum_comm
    _ ≤ ∑ _ℓ : Fin h, ∑ _side : Bool, b ^ h :=
        sum_le_sum fun ℓ _ => sum_le_sum fun side _ =>
          level_sum hb t ℓ side (fun o => f o side) (fun o => hf o side)
    _ = 2 * h * b ^ h := by simp; ring

theorem sum_len (hb : 2 ≤ b) (t : Fin (b ^ h)) :
    ∑ o, ∑ side, len b h o t side ≤ 2 * h * b ^ h := by
  apply sum_side_le hb t
  intro o side
  split_ifs with h0
  · rw [h0]
  · have := right_lt hb o t
    have := left_le o t
    have := t.isLt
    cases side <;> omega

theorem card_X_le (o : Fin (h * b)) (t : Fin (b ^ h)) (side : Bool) :
    (X b h o t side).card ≤ if len b h o t side = 0 then 0 else b ^ h := by
  unfold X
  split_ifs with h0
  · simp
  · exact (card_le_univ _).trans (by simp)

theorem sum_X (hb : 2 ≤ b) (t : Fin (b ^ h)) :
    ∑ o, ∑ side, (X b h o t side).card ≤ 2 * h * b ^ h :=
  sum_side_le hb t _ (fun o side => card_X_le o t side)

end sums

/-- The `b`-ary hierarchy as a lane system of depth `h`. -/
noncomputable def sys (hb : 2 ≤ b) (hh : 0 < h) : LaneSys (b ^ h) (h * b) where
  len := len b h
  X := X b h
  hop := hop b h hb hh
  lvl := lvl b h
  depth := h
  right_lt := right_lt hb
  left_le := left_le
  disj := disj hb
  avoid := avoid hb
  hop_in := hop_in hb hh
  hop_le := hop_le hb hh
  hop_ge := hop_ge hb hh
  hop_X := hop_X hb hh
  lvl_lt := lvl_lt hb hh
  lvl_hop := lvl_hop hb hh
  sum_len := sum_len hb
  sum_X := sum_X hb

end Hier

end SlidingPuzzle.Tree
