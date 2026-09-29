import SlidingPuzzle.Port.LandC

/-! # Insertion at the source of a hop

After the lane walk the blank sits on the insertion cell `v`, on the line of the
lane's port in the source square. A jump takes it to the rest cell `w` of the
port box next to `v`.

* Cheap insertion: a three-cycle in the port's corner box brings a class-`y` tile
  of the port to `v`; everything else stays in the port.
* Import: first a three-cycle in the corner box puts a class-`z` tile of the port
  on the cell `U1`; after the jump, a three-cycle in the square's box (staged at the
  same corner) sends a class-`y` tile from part `p` of the square to `v`, and the
  class-`z` tile to the class-`y` tile's cell. -/
namespace SlidingPuzzle.Port
open Classical
open SlidingPuzzle.Hub (Sq HDims sqOf classOf mkCell mkCell_fst mkCell_snd cell_ext InBox
  div_eq_iff_bounds exists_vjump_step exists_hjump_step exists_box_three_cycle_near cornerDist
  reflC apply_blank blank_eq_of_apply val_ne_zero_of_ne_blank)
open SlidingPuzzle.Hub.LayoutAux
open SlidingPuzzle.Tree

variable {n k s q σ : ℕ} (L : LaneSys k q)

/-! ## Local geometry -/

/-- Local coordinates of the line cell of offset `o` of the port of lanes like `l`. -/
def lineRC (k s : ℕ) (l : Ln k q) (o : ℕ) : ℕ × ℕ :=
  if l.1 then (if l.2.side then (s - 1, o) else (k, o)) else (if l.2.side then (o, s - 1) else (o, k))

/-- Local coordinates of the box cell next to it, of the parity needed for a jump. -/
def restRC (k s : ℕ) (l : Ln k q) (o : ℕ) : ℕ × ℕ :=
  if l.1 then (if l.2.side then (s - 2, k + 1 + (k + o + 1) % 2) else (k + 1, k + 1 + (k + o + 1) % 2))
  else (if l.2.side then (k + 1 + (k + o + 1) % 2, s - 2) else (k + 1 + (k + o + 1) % 2, k + 1))

/-- Spare box cells near the corner of a port. -/
def spare (k s : ℕ) : Pt → Fin 3 → ℕ × ℕ
  | .tl, i => (k + 3 + (if i.val = 2 then 1 else 0), k + 3 + (if i.val = 1 then 1 else 0))
  | .tr, i => (k + 3 + (if i.val = 2 then 1 else 0), s - 4 - (if i.val = 1 then 1 else 0))
  | .bl, i => (s - 4 - (if i.val = 1 then 1 else 0), k + 3 + (if i.val = 2 then 1 else 0))

/-- Top row of the corner box of a port. -/
def cr0 (k s σ : ℕ) : Pt → ℕ
  | .bl => s - (k + 2 + σ)
  | _ => 0

/-- Left column of the corner box of a port. -/
def cc0 (k s σ : ℕ) : Pt → ℕ
  | .tr => s - (k + 2 + σ)
  | _ => 0

/-- The corner of the box: bottom rows for `bl`. -/
def cfr : Pt → Bool
  | .bl => true
  | _ => false

/-- The corner of the box: right columns for `tr`. -/
def cfc : Pt → Bool
  | .tr => true
  | _ => false

theorem lport_cases (l : Ln k q) :
    (l.1 = true ∧ l.2.side = true ∧ lport l = .bl) ∨ (l.1 = true ∧ l.2.side = false ∧ lport l = .tl) ∨
      (l.1 = false ∧ l.2.side = true ∧ lport l = .tr) ∨
        (l.1 = false ∧ l.2.side = false ∧ lport l = .tl) := by
  unfold lport
  rcases l with ⟨_ | _, H⟩ <;> cases h : H.side <;> simp [h]

theorem rest_box (hσ : 2 ≤ σ) (hs : 2 * σ + 2 * k + 8 ≤ s) (l : Ln k q) (o : ℕ) :
    inBox k s σ (lport l) (restRC k s l o).1 (restRC k s l o).2 := by
  have h2 : (k + o + 1) % 2 ≤ 1 := by omega
  rcases lport_cases l with ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ <;>
    rw [h3] <;> simp only [restRC, h1, h2', if_true, if_false, Bool.false_eq_true, inBox] <;> omega

theorem spare_box (h4 : 4 ≤ σ) (hs : 2 * σ + 2 * k + 8 ≤ s) (pt : Pt) (i : Fin 3) :
    inBox k s σ pt (spare k s pt i).1 (spare k s pt i).2 := by
  have := i.isLt
  cases pt <;> simp only [spare, inBox] <;> split_ifs <;> omega

theorem spare_ne_rest (hs : 2 * σ + 2 * k + 8 ≤ s) (l : Ln k q) (o : ℕ) (i : Fin 3) :
    spare k s (lport l) i ≠ restRC k s l o := by
  have h2 : (k + o + 1) % 2 ≤ 1 := by omega
  have := i.isLt
  rcases lport_cases l with ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ <;>
    rw [h3] <;> simp only [restRC, spare, h1, h2', if_true, if_false, Bool.false_eq_true, ne_eq,
      Prod.mk.injEq] <;> split_ifs <;> omega

theorem spare_inj (hs : 2 * σ + 2 * k + 8 ≤ s) (pt : Pt) {i i' : Fin 3}
    (h : spare k s pt i = spare k s pt i') : i = i' := by
  have := i.isLt
  have := i'.isLt
  apply Fin.ext
  cases pt <;> simp only [spare, Prod.mk.injEq] at h <;> split_ifs at h <;> omega

/-- The corner box of a port contains its cells. -/
theorem portLoc_corner (hs : 2 * σ + 2 * k + 8 ≤ s) (hqk : q ≤ k) {pt : Pt} {r c : ℕ}
    (hrs : r < s) (hcs : c < s) (h : PortLoc k s q σ pt r c) :
    cr0 k s σ pt ≤ r ∧ r < cr0 k s σ pt + (k + 2 + σ) ∧
      cc0 k s σ pt ≤ c ∧ c < cc0 k s σ pt + (k + 2 + σ) := by
  cases pt <;> simp only [PortLoc, inBox, onLine, cr0, cc0] at h ⊢ <;> omega

theorem line_corner (hs : 2 * σ + 2 * k + 8 ≤ s) (hqk : q ≤ k) (l : Ln k q) {o : ℕ} (ho : o < q) :
    cr0 k s σ (lport l) ≤ (lineRC k s l o).1 ∧
      (lineRC k s l o).1 < cr0 k s σ (lport l) + (k + 2 + σ) ∧
      cc0 k s σ (lport l) ≤ (lineRC k s l o).2 ∧
      (lineRC k s l o).2 < cc0 k s σ (lport l) + (k + 2 + σ) := by
  rcases lport_cases l with ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ <;>
    rw [h3] <;> simp only [lineRC, h1, h2', if_true, if_false, Bool.false_eq_true, cr0, cc0] <;> omega

/-- Distances to the corner used by the three-cycles, in local coordinates. -/
def cdist (k s σ : ℕ) (pt : Pt) (r c : ℕ) : ℕ :=
  Nat.dist r (if cfr pt then s - 1 else 0) + Nat.dist c (if cfc pt then s - 1 else 0)

theorem cdist_line (hs : 2 * σ + 2 * k + 8 ≤ s) (hqk : q ≤ k) (l : Ln k q) {o : ℕ} (ho : o < q) :
    cdist k s σ (lport l) (lineRC k s l o).1 (lineRC k s l o).2 ≤ k + q := by
  rcases lport_cases l with ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ <;>
    rw [h3] <;> simp only [lineRC, cdist, cfr, cfc, h1, h2', if_true, if_false,
      Bool.false_eq_true, Nat.dist] <;> omega

theorem cdist_rest (hs : 2 * σ + 2 * k + 8 ≤ s) (l : Ln k q) (o : ℕ) :
    cdist k s σ (lport l) (restRC k s l o).1 (restRC k s l o).2 ≤ 2 * k + 3 := by
  have h2 : (k + o + 1) % 2 ≤ 1 := by omega
  rcases lport_cases l with ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ <;>
    rw [h3] <;> simp only [restRC, cdist, cfr, cfc, h1, h2', if_true, if_false,
      Bool.false_eq_true, Nat.dist] <;> omega

theorem cdist_spare (hs : 2 * σ + 2 * k + 8 ≤ s) (pt : Pt) (i : Fin 3) :
    cdist k s σ pt (spare k s pt i).1 (spare k s pt i).2 ≤ 2 * k + 8 := by
  have := i.isLt
  cases pt <;> simp only [spare, cdist, cfr, cfc, if_true, if_false, Bool.false_eq_true,
    Nat.dist] <;> split_ifs <;> omega

section board
variable [NeZero n]

set_option maxHeartbeats 4000000 in
/-- The corner distance of a three-cycle in a box sharing its corner with the square. -/
theorem cornerDist_le (pd : PDims n k s q σ) (Q : Sq k) (pt : Pt) {m : ℕ} (hm2 : 2 ≤ m)
    (hms : m ≤ s) {b1 b2 a1 a2 c1 c2 : ℕ} (hb1 : b1 < s) (hb2 : b2 < s) (ha1 : a1 < s)
    (ha2 : a2 < s) (hc1 : c1 < s) (hc2 : c2 < s) :
    cornerDist (Q.1.val * s + (if cfr pt then s - m else 0))
      (Q.2.val * s + (if cfc pt then s - m else 0))
      m (cfr pt) (cfc pt) (lc (n := n) s Q b1 b2) (lc s Q a1 a2) (lc s Q c1 c2) ≤
      (cdist k s σ pt b1 b2 + 1) + cdist k s σ pt a1 a2 + cdist k s σ pt c1 c2 := by
  have e1 := lc_fst (n := n) pd.hd Q b2 hb1
  have e2 := lc_snd (n := n) pd.hd Q b1 hb2
  have e3 := lc_fst (n := n) pd.hd Q a2 ha1
  have e4 := lc_snd (n := n) pd.hd Q a1 ha2
  have e5 := lc_fst (n := n) pd.hd Q c2 hc1
  have e6 := lc_snd (n := n) pd.hd Q c1 hc2
  generalize Q.1.val * s = R at *
  generalize Q.2.val * s = C at *
  unfold cornerDist reflC cdist
  rw [e1, e2, e3, e4, e5, e6]
  have d : ∀ a b c : ℕ, Nat.dist (a + b) (a + c) = Nat.dist b c := fun a b c => by
    simp only [Nat.dist]; omega
  have d0 : ∀ a b : ℕ, Nat.dist (a + b) a = b := fun a b => by
    simp only [Nat.dist]; omega
  have t1 : ∀ b : ℕ, Nat.dist b 1 ≤ Nat.dist b 0 + 1 := fun b => by simp only [Nat.dist]; omega
  have t2 : ∀ b : ℕ, b < s → Nat.dist b (s - 2) ≤ Nat.dist b (s - 1) + 1 := fun b _ => by
    simp only [Nat.dist]; omega
  have z : ∀ b : ℕ, Nat.dist b 0 = b := fun b => by simp only [Nat.dist]; omega
  cases pt
  · simp only [cfr, cfc, if_false, Bool.false_eq_true, add_zero, d, d0]
    have := t1 b1; simp only [z] at this ⊢; omega
  · simp only [cfr, cfc, if_true, if_false, Bool.false_eq_true, add_zero]
    rw [show C + (s - m) + (m - 1 - 0) = C + (s - 1) by omega]
    simp only [d, d0]
    have := t1 b1; simp only [z] at this ⊢; omega
  · simp only [cfr, cfc, if_true, if_false, Bool.false_eq_true, add_zero]
    rw [show R + (s - m) + (m - 1 - 1) = R + (s - 2) by omega,
      show R + (s - m) + (m - 1 - 0) = R + (s - 1) by omega]
    simp only [d, d0]
    have := t2 b1 hb1; simp only [z] at this ⊢; omega

end board

end SlidingPuzzle.Port
