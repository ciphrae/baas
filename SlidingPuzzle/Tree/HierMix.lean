import SlidingPuzzle.Tree.Hier

/-! # Hierarchies with per-level branching

As `Hier`, but level `ℓ < h` splits a node into `B ℓ` children. A node at level `ℓ`
has `sz ℓ = ∏_{ℓ ≤ j < h} B j` blocks, so there are `k = sz 0` blocks and
`q = ∑_{ℓ < h} B ℓ` offsets `o ↔ ⟨ℓ, i⟩` (`finSigmaFinEquiv`). -/
namespace SlidingPuzzle.Tree

namespace HierMix

open Finset
open Hier (div_eq_of_bounds right_piece left_piece mod_lt_mul sum_le_of_unique)

variable (B : ℕ → ℕ) (h : ℕ)

/-- Blocks of a node at level `ℓ`. -/
def sz (ℓ : ℕ) : ℕ := ∏ j ∈ Ico ℓ h, B j

/-- Number of offsets. -/
abbrev nq : ℕ := ∑ ℓ : Fin h, B ℓ

/-- Level of an offset. -/
def lev (o : Fin (nq B h)) : ℕ := (finSigmaFinEquiv.symm o).1.val

/-- Child index of an offset. -/
def chi (o : Fin (nq B h)) : ℕ := (finSigmaFinEquiv.symm o).2.val

/-- Branching at the level of an offset. -/
def bra (o : Fin (nq B h)) : ℕ := B (lev B h o)

/-- Child size at the level of an offset. -/
def csz (o : Fin (nq B h)) : ℕ := sz B h (lev B h o + 1)

theorem lev_lt (o : Fin (nq B h)) : lev B h o < h := (finSigmaFinEquiv.symm o).1.isLt

theorem chi_lt (o : Fin (nq B h)) : chi B h o < bra B h o := (finSigmaFinEquiv.symm o).2.isLt

theorem sz_succ {ℓ : ℕ} (hℓ : ℓ < h) : sz B h ℓ = B ℓ * sz B h (ℓ + 1) := by
  unfold sz; rw [prod_eq_prod_Ico_succ_bot hℓ]

theorem sz_split {a c : ℕ} (hac : a ≤ c) (hc : c ≤ h) :
    sz B h a = (∏ j ∈ Ico a c, B j) * sz B h c := by
  unfold sz; rw [prod_Ico_consecutive _ hac hc]

section sizes

variable {B h} (hB : ∀ ℓ, 2 ≤ B ℓ)
include hB

theorem sz_pos (ℓ : ℕ) : 0 < sz B h ℓ :=
  prod_pos fun j _ => by have := hB j; omega

omit hB in
theorem sz_dvd (ℓ : ℕ) : sz B h ℓ ∣ sz B h 0 := by
  rcases le_or_gt ℓ h with hl | hl
  · rw [sz_split B h (Nat.zero_le ℓ) hl]; exact dvd_mul_left _ _
  · have : sz B h ℓ = 1 := by unfold sz; rw [Ico_eq_empty (by omega), prod_empty]
    rw [this]; exact one_dvd _

omit hB in
theorem parent_eq (o : Fin (nq B h)) : bra B h o * csz B h o = sz B h (lev B h o) :=
  (sz_succ B h (lev_lt B h o)).symm

theorem csz_pos (o : Fin (nq B h)) : 0 < csz B h o := sz_pos hB _

theorem bra_pos (o : Fin (nq B h)) : 0 < bra B h o := by have := hB (lev B h o); unfold bra; omega

end sizes

/-- Piece lengths. -/
def len (o : Fin (nq B h)) (t : Fin (sz B h 0)) (side : Bool) : ℕ :=
  if side then
    (if t.val % (bra B h o * csz B h o) = chi B h o * csz B h o + (csz B h o - 1) then
      (bra B h o - 1 - chi B h o) * csz B h o else 0)
  else
    (if t.val % (bra B h o * csz B h o) = chi B h o * csz B h o then chi B h o * csz B h o else 0)

/-- Target blocks routed through a piece: the blocks of the child. -/
def X (o : Fin (nq B h)) (t : Fin (sz B h 0)) (side : Bool) : Finset (Fin (sz B h 0)) :=
  if len B h o t side = 0 then ∅ else univ.filter fun c => c.val / csz B h o = t.val / csz B h o

/-- `J` and `c` lie in different children at level `ℓ`. -/
def Sep (J c : ℕ) (ℓ : ℕ) : Prop := ℓ < h ∧ J / sz B h (ℓ + 1) ≠ c / sz B h (ℓ + 1)

instance (J c ℓ : ℕ) : Decidable (Sep B h J c ℓ) := by unfold Sep; infer_instance

theorem sep_exists {J c : ℕ} (hh : 0 < h) (hne : J ≠ c) : ∃ ℓ, Sep B h J c ℓ := by
  refine ⟨h - 1, by omega, ?_⟩
  have : sz B h (h - 1 + 1) = 1 := by unfold sz; rw [Ico_eq_empty (by omega), prod_empty]
  rw [this]; simpa using hne

open Classical in
/-- The level of a hop (`0` if `J = c`). -/
noncomputable def lvl (J c : Fin (sz B h 0)) : ℕ :=
  if hx : ∃ ℓ, Sep B h J.val c.val ℓ then Nat.find hx else 0

/-- The offset `⟨ℓ, i⟩`. -/
def mk (ℓ : ℕ) (hℓ : ℓ < h) (i : ℕ) (hi : i < B ℓ) : Fin (nq B h) :=
  finSigmaFinEquiv ⟨⟨ℓ, hℓ⟩, ⟨i, hi⟩⟩

theorem lev_mk (ℓ : ℕ) (hℓ : ℓ < h) (i : ℕ) (hi : i < B ℓ) : lev B h (mk B h ℓ hℓ i hi) = ℓ := by
  simp [lev, mk]

theorem chi_mk (ℓ : ℕ) (hℓ : ℓ < h) (i : ℕ) (hi : i < B ℓ) : chi B h (mk B h ℓ hℓ i hi) = i := by
  unfold chi mk; rw [Equiv.symm_apply_apply]

theorem land_lt {M K c : ℕ} (hM : 0 < M) (hd : M ∣ K) (hc : c < K) : c / M * M + (M - 1) < K := by
  obtain ⟨r, rfl⟩ := hd
  have h2 : c / M < r := Nat.div_lt_of_lt_mul hc
  have h3 : (c / M + 1) * M ≤ r * M := Nat.mul_le_mul_right M h2
  rw [add_mul, one_mul, mul_comm r M] at h3
  omega

open Classical in
/-- The hop from `J` toward `c`. -/
noncomputable def hop (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 0 < h) (J c : Fin (sz B h 0)) :
    Fin (nq B h) × Fin (sz B h 0) :=
  if hx : ∃ ℓ, Sep B h J.val c.val ℓ then
    let ℓ := Nat.find hx
    let m := sz B h (ℓ + 1)
    have hℓ : ℓ < h := (Nat.find_spec hx).1
    have hm : 0 < m := sz_pos hB _
    have hk : c.val / m * m + (m - 1) < sz B h 0 := land_lt hm (sz_dvd (ℓ + 1)) c.isLt
    (mk B h ℓ hℓ ((c.val / m) % B ℓ) (Nat.mod_lt _ (by have := hB ℓ; omega)),
      ⟨if J.val < c.val then c.val / m * m else c.val / m * m + (m - 1), by
        split_ifs <;> omega⟩)
  else (⟨0, by
      have : B 0 ≤ nq B h := by
        unfold nq
        exact single_le_sum (f := fun ℓ : Fin h => B ℓ) (fun _ _ => Nat.zero_le _)
          (mem_univ (⟨0, hh⟩ : Fin h))
      have := hB 0; omega⟩, J)

/-! ## The hop in coordinates -/

section spec

variable {B h} (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 0 < h)
include hB hh

omit hB in
theorem sep_of_ne {J c : Fin (sz B h 0)} (hne : J ≠ c) : ∃ ℓ, Sep B h J.val c.val ℓ :=
  sep_exists B h hh (fun e => hne (Fin.ext e))

/-- Everything about the hop from `J` toward `c ≠ J`. -/
theorem hop_spec {J c : Fin (sz B h 0)} (hne : J ≠ c) :
    ∃ ℓ i, ℓ < h ∧ i < B ℓ ∧ lvl B h J c = ℓ ∧
      lev B h (hop B h hB hh J c).1 = ℓ ∧ chi B h (hop B h hB hh J c).1 = i ∧
      bra B h (hop B h hB hh J c).1 = B ℓ ∧
      csz B h (hop B h hB hh J c).1 = sz B h (ℓ + 1) ∧
      i = (c.val / sz B h (ℓ + 1)) % B ℓ ∧
      (hop B h hB hh J c).2.val = (if J.val < c.val then c.val / sz B h (ℓ + 1) * sz B h (ℓ + 1)
        else c.val / sz B h (ℓ + 1) * sz B h (ℓ + 1) + (sz B h (ℓ + 1) - 1)) ∧
      J.val / sz B h (ℓ + 1) ≠ c.val / sz B h (ℓ + 1) ∧
      J.val / (B ℓ * sz B h (ℓ + 1)) = c.val / (B ℓ * sz B h (ℓ + 1)) ∧
      (∀ ℓ' < ℓ, ¬ Sep B h J.val c.val ℓ') := by
  classical
  have hx := sep_of_ne hh hne
  set ℓ := Nat.find hx with hℓdef
  have hsp := Nat.find_spec hx
  have hmin : ∀ ℓ' < ℓ, ¬ Sep B h J.val c.val ℓ' := fun ℓ' h' => Nat.find_min hx h'
  have hℓ : ℓ < h := hsp.1
  have hlev : lev B h (hop B h hB hh J c).1 = ℓ := by
    unfold hop; rw [dif_pos hx]; simp only [lev_mk]; rfl
  refine ⟨ℓ, (c.val / sz B h (ℓ + 1)) % B ℓ, hℓ, Nat.mod_lt _ (by have := hB ℓ; omega), ?_,
    hlev, ?_, ?_, ?_, rfl, ?_, hsp.2, ?_, hmin⟩
  · unfold lvl; rw [dif_pos hx]
  · unfold hop; rw [dif_pos hx]; simp only [chi_mk]; rfl
  · unfold bra; rw [hlev]
  · unfold csz; rw [hlev]
  · unfold hop; rw [dif_pos hx]
  · -- same parent
    rw [← sz_succ B h hℓ]
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · rw [h0, Nat.div_eq_of_lt J.isLt, Nat.div_eq_of_lt c.isLt]
    · have := hmin (ℓ - 1) (by omega)
      unfold Sep at this
      push Not at this
      have e2 : ℓ - 1 + 1 = ℓ := by omega
      rw [e2] at this
      exact this (by omega)

end spec

/-! ## Pieces -/

section pieces

variable {B h} (hB : ∀ ℓ, 2 ≤ B ℓ)
include hB

omit hB in
theorem parent_dvd (o : Fin (nq B h)) : bra B h o * csz B h o ∣ sz B h 0 := by
  rw [parent_eq]; exact sz_dvd _

/-- A block in a piece: same parent as the landing block, and on the correct side
of the child. -/
theorem inPiece_spec {o : Fin (nq B h)} {t : Fin (sz B h 0)} {side : Bool} {J : ℕ}
    (hJ : InPiece (len B h o t side) t.val side J) :
    J / (bra B h o * csz B h o) = t.val / (bra B h o * csz B h o) ∧
      t.val % (bra B h o * csz B h o) = (if side then chi B h o * csz B h o + (csz B h o - 1)
        else chi B h o * csz B h o) ∧
      (if side then chi B h o * csz B h o + (csz B h o - 1) < J % (bra B h o * csz B h o)
        else J % (bra B h o * csz B h o) < chi B h o * csz B h o) := by
  have hm := csz_pos hB o
  have hi := chi_lt B h o
  have hb := bra_pos hB o
  cases side
  · simp only [len, Bool.false_eq_true, if_false] at hJ ⊢
    split_ifs at hJ with ht
    · obtain ⟨h1, h2⟩ := left_piece hm ht hJ.1 hJ.2 hb
      exact ⟨h1, ht, h2⟩
    · unfold InPiece at hJ; simp at hJ; omega
  · simp only [len, if_true] at hJ ⊢
    split_ifs at hJ with ht
    · obtain ⟨h1, h2⟩ := right_piece hm hi ht hJ.1 hJ.2
      exact ⟨h1, ht, h2⟩
    · unfold InPiece at hJ; simp at hJ; omega

theorem right_lt (o : Fin (nq B h)) (t : Fin (sz B h 0)) :
    t.val + len B h o t true < sz B h 0 := by
  have hm := csz_pos hB o
  have hi := chi_lt B h o
  have hb := bra_pos hB o
  simp only [len, if_true]
  split_ifs with ht
  · set P := bra B h o * csz B h o with hP
    have hM : 0 < P := Nat.mul_pos hb hm
    have e := Nat.div_add_mod t.val P
    obtain ⟨r, hr⟩ := parent_dvd o
    rw [← hP] at hr
    have h1 : t.val / P < r := by
      apply Nat.div_lt_of_lt_mul; rw [← hr]; exact t.isLt
    have h2 : P * (t.val / P + 1) ≤ P * r := Nat.mul_le_mul_left _ h1
    rw [← hr, mul_add, mul_one] at h2
    have hbm : (bra B h o - 1 - chi B h o) * csz B h o + (chi B h o * csz B h o + (csz B h o - 1)) =
        P - 1 := by
      have : (bra B h o - 1 - chi B h o) + chi B h o + 1 = bra B h o := by omega
      have h3 : ((bra B h o - 1 - chi B h o) + chi B h o + 1) * csz B h o = P := by rw [this]
      rw [add_mul, add_mul, one_mul] at h3
      omega
    omega
  · simp only [add_zero]; exact t.isLt

omit hB in
theorem left_le (o : Fin (nq B h)) (t : Fin (sz B h 0)) : len B h o t false ≤ t.val := by
  simp only [len, Bool.false_eq_true, if_false]
  split_ifs with ht
  · rw [← ht]; exact Nat.mod_le _ _
  · exact Nat.zero_le _

theorem disj (o : Fin (nq B h)) (t t' : Fin (sz B h 0)) (side side' : Bool) (J : ℕ)
    (h1 : InPiece (len B h o t side) t side J) (h2 : InPiece (len B h o t' side') t' side' J) :
    t = t' ∧ side = side' := by
  obtain ⟨a1, a2, a3⟩ := inPiece_spec hB h1
  obtain ⟨b1, b2, b3⟩ := inPiece_spec hB h2
  have key : t.val / (bra B h o * csz B h o) = t'.val / (bra B h o * csz B h o) := a1.symm.trans b1
  have fin : t.val % (bra B h o * csz B h o) = t'.val % (bra B h o * csz B h o) → t = t' :=
    fun hmod => Fin.ext (by rw [← Nat.div_add_mod t.val (bra B h o * csz B h o),
      ← Nat.div_add_mod t'.val (bra B h o * csz B h o), key, hmod])
  cases side <;> cases side'
  · exact ⟨fin (by simpa using a2.trans b2.symm), rfl⟩
  · simp only [Bool.false_eq_true, if_false, if_true] at a3 b3; omega
  · simp only [Bool.false_eq_true, if_false, if_true] at a3 b3; omega
  · exact ⟨fin (by simpa using a2.trans b2.symm), rfl⟩

theorem avoid (o : Fin (nq B h)) (t t' : Fin (sz B h 0)) (side side' : Bool)
    (hpos : 0 < len B h o t side) : ¬ InPiece (len B h o t' side') t' side' t.val := by
  intro hin
  obtain ⟨-, -, a3⟩ := inPiece_spec hB hin
  have hm := csz_pos hB o
  have ht : t.val % (bra B h o * csz B h o) = (if side then chi B h o * csz B h o + (csz B h o - 1)
      else chi B h o * csz B h o) := by
    cases side <;> simp only [len, Bool.false_eq_true, if_false, if_true] at hpos ⊢ <;>
      split_ifs at hpos with hh <;> first | exact hh | omega
  cases side <;> cases side' <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> omega

end pieces

/-! ## Hops -/

section hops

variable {B h} (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 0 < h)
include hB hh

/-- The landing block of a hop, as a multiple of the child size. -/
theorem hop_land {J c : Fin (sz B h 0)} (hne : J ≠ c) :
    ∃ ℓ i A P, ℓ < h ∧ i < B ℓ ∧ lvl B h J c = ℓ ∧
      lev B h (hop B h hB hh J c).1 = ℓ ∧ chi B h (hop B h hB hh J c).1 = i ∧
      bra B h (hop B h hB hh J c).1 = B ℓ ∧
      csz B h (hop B h hB hh J c).1 = sz B h (ℓ + 1) ∧
      c.val / sz B h (ℓ + 1) = A ∧ A = P * B ℓ + i ∧
      c.val / (B ℓ * sz B h (ℓ + 1)) = P ∧ J.val / (B ℓ * sz B h (ℓ + 1)) = P ∧
      J.val / sz B h (ℓ + 1) ≠ A ∧
      (hop B h hB hh J c).2.val = (if J.val < c.val then A * sz B h (ℓ + 1)
        else A * sz B h (ℓ + 1) + (sz B h (ℓ + 1) - 1)) ∧
      (∀ ℓ' < ℓ, ¬ Sep B h J.val c.val ℓ') := by
  obtain ⟨ℓ, i, hℓ, hi, e1, e2, e3, eb, e4, e5, e6, e7, e8, e9⟩ := hop_spec hB hh hne
  refine ⟨ℓ, i, c.val / sz B h (ℓ + 1), c.val / (B ℓ * sz B h (ℓ + 1)), hℓ, hi, e1, e2, e3, eb, e4,
    rfl, ?_, rfl, e8.trans rfl, e7, e6, e9⟩
  rw [e5, Nat.mul_comm (B ℓ), ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ (B ℓ)).symm

theorem hop_in (J c : Fin (sz B h 0)) (hne : J ≠ c) :
    InPiece (len B h (hop B h hB hh J c).1 (hop B h hB hh J c).2 (decide (c < J)))
      (hop B h hB hh J c).2 (decide (c < J)) J.val := by
  obtain ⟨ℓ, i, A, P, hℓ, hi, -, -, e3, eb, e4, eA, eAP, eP, eJ, hJA, et, -⟩ := hop_land hB hh hne
  set m := sz B h (ℓ + 1) with hm_def
  set b := B ℓ with hb_def
  have hm : 0 < m := sz_pos hB _
  have hb2 : 2 ≤ b := hB ℓ
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
    have htv : (hop B h hB hh J c).2.val = A * m := by rw [et, if_pos hlt]
    have hmod : (hop B h hB hh J c).2.val % (b * m) = i * m := by
      rw [htv, hPM, mul_comm P, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    unfold InPiece len
    simp only [Bool.false_eq_true, if_false]
    rw [e3, eb, e4, hmod, if_pos rfl]
    rw [mul_comm m (J.val / m)] at eJm
    rw [mul_comm (b * m)] at eJ2
    constructor <;> omega
  · have hd : decide (c < J) = true := by simp; exact hlt
    rw [hd]
    have hle : A ≤ J.val / m := eA ▸ Nat.div_le_div_right hlt.le
    have hlt2 : A + 1 ≤ J.val / m := by omega
    have h3 : (A + 1) * m ≤ J.val / m * m := Nat.mul_le_mul_right m hlt2
    rw [add_mul, one_mul] at h3
    have htv : (hop B h hB hh J c).2.val = A * m + (m - 1) := by
      rw [et, if_neg (by omega)]
    have hmod : (hop B h hB hh J c).2.val % (b * m) = i * m + (m - 1) := by
      rw [htv, hPM, mul_comm P, add_assoc, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    unfold InPiece len
    simp only [if_true]
    rw [e3, eb, e4, hmod, if_pos rfl]
    rw [mul_comm m (J.val / m)] at eJm
    rw [mul_comm (b * m)] at eJ2
    have hbm : (b - 1 - i) * m + (i * m + (m - 1)) = b * m - 1 := by
      have : (b - 1 - i) + i + 1 = b := by omega
      have h4 : ((b - 1 - i) + i + 1) * m = b * m := by rw [this]
      rw [add_mul, add_mul, one_mul] at h4
      omega
    constructor <;> omega

theorem hop_le (J c : Fin (sz B h 0)) (hlt : J < c) : (hop B h hB hh J c).2 ≤ c := by
  obtain ⟨ℓ, i, A, P, -, -, -, -, -, -, -, eA, -, -, -, -, et, -⟩ := hop_land hB hh (ne_of_lt hlt)
  show (hop B h hB hh J c).2.val ≤ c.val
  rw [et, if_pos (show J.val < c.val from hlt), ← eA]
  exact Nat.div_mul_le_self _ _

theorem hop_ge (J c : Fin (sz B h 0)) (hlt : c < J) : c ≤ (hop B h hB hh J c).2 := by
  obtain ⟨ℓ, i, A, P, -, -, -, -, -, -, -, eA, -, -, -, -, et, -⟩ := hop_land hB hh (ne_of_gt hlt)
  show c.val ≤ (hop B h hB hh J c).2.val
  have hm : 0 < sz B h (ℓ + 1) := sz_pos hB _
  have := Nat.div_add_mod c.val (sz B h (ℓ + 1))
  have := Nat.mod_lt c.val hm
  rw [et, if_neg (by have : c.val < J.val := hlt; omega), ← eA, mul_comm]
  omega

/-- The landing block lies in the target's child. -/
theorem hop_child {J c : Fin (sz B h 0)} (hne : J ≠ c) :
    (hop B h hB hh J c).2.val / csz B h (hop B h hB hh J c).1 =
      c.val / csz B h (hop B h hB hh J c).1 := by
  obtain ⟨ℓ, i, A, P, -, -, -, -, -, -, e4, eA, -, -, -, -, et, -⟩ := hop_land hB hh hne
  have hm : 0 < sz B h (ℓ + 1) := sz_pos hB _
  rw [e4, eA, et]
  split_ifs
  · exact Nat.mul_div_cancel _ hm
  · apply div_eq_of_bounds <;> omega

theorem hop_X (J c : Fin (sz B h 0)) (hne : J ≠ c) :
    c ∈ X B h (hop B h hB hh J c).1 (hop B h hB hh J c).2 (decide (c < J)) := by
  have hin := hop_in hB hh J c hne
  unfold X
  rw [if_neg]
  · simp only [mem_filter, mem_univ, true_and]
    exact (hop_child hB hh hne).symm
  · intro h0
    rw [h0] at hin
    unfold InPiece at hin
    split at hin <;> omega

theorem lvl_lt (J c : Fin (sz B h 0)) (hne : J ≠ c) : lvl B h J c < h := by
  obtain ⟨ℓ, -, hℓ, -, e1, -⟩ := hop_spec hB hh hne
  rw [e1]; exact hℓ

theorem lvl_hop (J c : Fin (sz B h 0)) (hne : J ≠ c) (ht : (hop B h hB hh J c).2 ≠ c) :
    lvl B h J c < lvl B h (hop B h hB hh J c).2 c := by
  have hch := hop_child hB hh hne
  obtain ⟨ℓ, -, hℓ, -, e1, -, -, -, e4, -⟩ := hop_spec hB hh hne
  obtain ⟨ℓ2, -, hℓ2, -, f1, -, -, -, -, -, -, f7, -⟩ := hop_spec hB hh ht
  rw [e1, f1]
  by_contra hle
  push Not at hle
  rw [e4] at hch
  apply f7
  have e : sz B h (ℓ2 + 1) = sz B h (ℓ + 1) * ∏ j ∈ Ico (ℓ2 + 1) (ℓ + 1), B j := by
    rw [sz_split B h (show ℓ2 + 1 ≤ ℓ + 1 by omega) (show ℓ + 1 ≤ h by omega), mul_comm]
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hch]

end hops

/-! ## Sums at a landing block -/

section sums

variable {B h} (hB : ∀ ℓ, 2 ≤ B ℓ)
include hB

omit hB in
theorem csz_mk (ℓ : ℕ) (hℓ : ℓ < h) (i : ℕ) (hi : i < B ℓ) :
    csz B h (mk B h ℓ hℓ i hi) = sz B h (ℓ + 1) := by
  unfold csz; rw [lev_mk]

omit hB in
theorem bra_mk (ℓ : ℕ) (hℓ : ℓ < h) (i : ℕ) (hi : i < B ℓ) :
    bra B h (mk B h ℓ hℓ i hi) = B ℓ := by
  unfold bra; rw [lev_mk]

/-- Per level and side, at most one child has a nonempty piece landing at `t`. -/
theorem level_sum (t : Fin (sz B h 0)) (ℓ : Fin h) (side : Bool) (f : Fin (nq B h) → ℕ)
    (hf : ∀ o, f o ≤ if len B h o t side = 0 then 0 else sz B h 0) :
    ∑ i : Fin (B ℓ), f (mk B h ℓ ℓ.isLt i i.isLt) ≤ sz B h 0 := by
  set m := sz B h (ℓ.val + 1)
  have hm : 0 < m := sz_pos hB _
  apply sum_le_of_unique _ (fun i : Fin (B ℓ) => t.val % (B ℓ * m) =
    (if side then i.val * m + (m - 1) else i.val * m)) (sz B h 0)
  · intro i j hi hj
    apply Fin.ext
    have e := hi.symm.trans hj
    exact Nat.eq_of_mul_eq_mul_right hm (show i.val * m = j.val * m by split_ifs at e <;> omega)
  · intro i
    refine (hf _).trans ?_
    by_cases hl : len B h (mk B h ℓ ℓ.isLt i i.isLt) t side = 0
    · rw [if_pos hl]; exact Nat.zero_le _
    · rw [if_neg hl, if_pos]
      simp only [len, chi_mk, csz_mk, bra_mk] at hl
      cases side <;> simp only [Bool.false_eq_true, if_false, if_true] at hl ⊢ <;>
        split_ifs at hl with hc <;> first | exact hc | exact absurd rfl hl

omit hB in
theorem sum_offsets (f : Fin (nq B h) → ℕ) :
    ∑ o, f o = ∑ ℓ : Fin h, ∑ i : Fin (B ℓ), f (mk B h ℓ ℓ.isLt i i.isLt) := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  rfl

theorem sum_side_le (t : Fin (sz B h 0)) (f : Fin (nq B h) → Bool → ℕ)
    (hf : ∀ o side, f o side ≤ if len B h o t side = 0 then 0 else sz B h 0) :
    ∑ o, ∑ side, f o side ≤ 2 * h * sz B h 0 := by
  rw [sum_offsets]
  calc ∑ ℓ : Fin h, ∑ i : Fin (B ℓ), ∑ side, f (mk B h ℓ ℓ.isLt i i.isLt) side
      = ∑ ℓ : Fin h, ∑ side, ∑ i : Fin (B ℓ), f (mk B h ℓ ℓ.isLt i i.isLt) side := by
        refine sum_congr rfl fun ℓ _ => sum_comm
    _ ≤ ∑ _ℓ : Fin h, ∑ _side : Bool, sz B h 0 :=
        sum_le_sum fun ℓ _ => sum_le_sum fun side _ =>
          level_sum hB t ℓ side (fun o => f o side) (fun o => hf o side)
    _ = 2 * h * sz B h 0 := by simp; ring

theorem sum_len (t : Fin (sz B h 0)) :
    ∑ o, ∑ side, len B h o t side ≤ 2 * h * sz B h 0 := by
  apply sum_side_le hB t
  intro o side
  split_ifs with h0
  · rw [h0]
  · have := right_lt hB o t
    have := left_le o t
    have := t.isLt
    cases side <;> omega

omit hB in
theorem card_X_le (o : Fin (nq B h)) (t : Fin (sz B h 0)) (side : Bool) :
    (X B h o t side).card ≤ if len B h o t side = 0 then 0 else sz B h 0 := by
  unfold X
  split_ifs with h0
  · simp
  · exact (card_le_univ _).trans (by simp)

theorem sum_X (t : Fin (sz B h 0)) :
    ∑ o, ∑ side, (X B h o t side).card ≤ 2 * h * sz B h 0 :=
  sum_side_le hB t _ (fun o side => card_X_le o t side)

theorem X_le (o : Fin (nq B h)) (t : Fin (sz B h 0)) (side : Bool) :
    (X B h o t side).card ≤ len B h o t side := by
  unfold X
  split_ifs with h0
  · simp
  · have hm := csz_pos hB o
    have hcard : (univ.filter fun c : Fin (sz B h 0) => c.val / csz B h o = t.val / csz B h o).card
        ≤ csz B h o := by
      refine (card_le_card_of_injOn (fun c => c.val % csz B h o) (t := range (csz B h o))
        ?_ ?_).trans (card_range _).le
      · intro c _; simp only [coe_range, Set.mem_Iio]; exact Nat.mod_lt _ hm
      · intro c hc c' hc' he
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc hc'
        apply Fin.ext
        rw [← Nat.div_add_mod c.val (csz B h o), ← Nat.div_add_mod c'.val (csz B h o), hc, hc']
        simp only at he; rw [he]
    refine hcard.trans ?_
    have hi := chi_lt B h o
    unfold len at h0 ⊢
    cases side
    · simp only [Bool.false_eq_true, if_false] at h0 ⊢
      split_ifs at h0 ⊢ with ht
      · have : 1 ≤ chi B h o := by
          by_contra hc; push Not at hc
          have : chi B h o = 0 := by omega
          rw [this, zero_mul] at h0; exact h0 rfl
        calc csz B h o = 1 * csz B h o := (one_mul _).symm
          _ ≤ chi B h o * csz B h o := Nat.mul_le_mul_right _ this
      · exact absurd rfl h0
    · simp only [if_true] at h0 ⊢
      split_ifs at h0 ⊢ with ht
      · have : 1 ≤ bra B h o - 1 - chi B h o := by
          by_contra hc; push Not at hc
          have : bra B h o - 1 - chi B h o = 0 := by omega
          rw [this, zero_mul] at h0; exact h0 rfl
        calc csz B h o = 1 * csz B h o := (one_mul _).symm
          _ ≤ (bra B h o - 1 - chi B h o) * csz B h o := Nat.mul_le_mul_right _ this
      · exact absurd rfl h0

end sums

/-- The mixed hierarchy as a lane system of depth `h`. -/
noncomputable def sys (hB : ∀ ℓ, 2 ≤ B ℓ) (hh : 0 < h) : LaneSys (sz B h 0) (nq B h) where
  len := len B h
  X := X B h
  hop := hop B h hB hh
  lvl := lvl B h
  depth := h
  right_lt := right_lt hB
  left_le := left_le
  disj := disj hB
  avoid := avoid hB
  hop_in := hop_in hB hh
  hop_le := hop_le hB hh
  hop_ge := hop_ge hB hh
  hop_X := hop_X hB hh
  lvl_lt := lvl_lt hB hh
  lvl_hop := lvl_hop hB hh
  sum_len := sum_len hB
  sum_X := sum_X hB
  X_le := X_le hB

end HierMix

end SlidingPuzzle.Tree
