import SlidingPuzzle.Port.GhostOps

/-! # Surplus classes and the choice of insertion modes

A part of a square has a *surplus* of class `z` when it holds more class-`z` tiles than
its demand. Surpluses exist as long as ports are larger than the stock of their
square (`surplus_port`), and a square holding a class beyond its demanded stock has
it in some part (`surplus_part`). The choice functions pick them. -/
namespace SlidingPuzzle.Port
open Finset
open SlidingPuzzle.Hub (Sq)
open SlidingPuzzle.Tree

variable {k q : ℕ} (L : LaneSys k q)

/-- The size of a port: its tiles plus the blank, a constant of the run. -/
def psz (σ0 : PState k q) (Q : Sq k) (pt : Pt) : ℕ :=
  (∑ z, σ0.pc Q pt z) + (if σ0.blank = Q ∧ σ0.bp = pt then 1 else 0)

theorem dem_le_stk (G : PG k q) (Q : Sq k) (pt : Pt) (z : Sq k) :
    dem L G Q (some pt) z ≤ G.stk Q z := by
  unfold PG.stk
  show (if z ≠ Q ∧ dport L Q z = pt then G.stock Q pt z else 0) ≤ _
  split_ifs
  · exact Finset.single_le_sum (f := fun pt => G.stock Q pt z) (fun _ _ => Nat.zero_le _)
      (mem_univ pt)
  · exact Nat.zero_le _

section surplus
variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

theorem surplus_port {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) (Q : Sq k) (pt : Pt)
    (h : (∑ z, G.stk Q z) + 1 < psz σ0 Q pt) : ∃ c, dem L G Q (some pt) c < G.σ.pc Q pt c := by
  by_contra hne
  push Not at hne
  have h1 : (∑ z, G.σ.pc Q pt z) ≤ ∑ z, G.stk Q z :=
    sum_le_sum fun z _ => (hne z).trans (dem_le_stk L G Q pt z)
  have h2 := hL.psum Q pt
  have h3 : (if G.σ.blank = Q ∧ G.σ.bp = pt then 1 else 0) ≤ 1 := by split_ifs <;> omega
  unfold psz at h
  omega

theorem sum_part (f : Part → ℕ) : ∑ p, f p = f none + ∑ pt, f (some pt) :=
  Fintype.sum_option f

theorem sum_partCnt {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) (Q y : Sq k) :
    ∑ p, G.σ.partCnt Q p y = G.σ.cnt Q y := by
  rw [sum_part]
  have := hL.pc_le Q y
  simp only [PState.partCnt, PState.mcnt]
  omega

theorem sum_dem (G : PG k q) (Q y : Sq k) :
    ∑ p, dem L G Q p y = if y ≠ Q then G.stock Q (dport L Q y) y else 0 := by
  rw [sum_part]
  simp only [dem, zero_add]
  split_ifs with h
  · rw [Finset.sum_eq_single (dport L Q y)]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · apply Finset.sum_eq_zero; intro b _; simp at h; simp [h]

theorem surplus_part {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) (Q y : Sq k)
    (h : G.stock Q (dport L Q y) y < G.σ.cnt Q y) :
    ∃ p, dem L G Q p y < G.σ.partCnt Q p y := by
  by_contra hne
  push Not at hne
  have h1 : ∑ p, G.σ.partCnt Q p y ≤ ∑ p, dem L G Q p y := sum_le_sum fun p _ => hne p
  rw [sum_partCnt L hL, sum_dem] at h1
  split_ifs at h1 <;> omega

end surplus

/-! ## Choices -/

open Classical in
/-- A surplus class of port `pt` of `Q`. -/
noncomputable def pickSur (G : PG k q) (Q : Sq k) (pt : Pt) : Sq k :=
  if h : ∃ c, dem L G Q (some pt) c < G.σ.pc Q pt c then Classical.choose h else Q

theorem pickSur_spec (G : PG k q) (Q : Sq k) (pt : Pt)
    (h : ∃ c, dem L G Q (some pt) c < G.σ.pc Q pt c) :
    dem L G Q (some pt) (pickSur L G Q pt) < G.σ.pc Q pt (pickSur L G Q pt) := by
  unfold pickSur; rw [dif_pos h]; exact Classical.choose_spec h

open Classical in
/-- A part of `Q` other than port `P` with a surplus of class `y`. -/
noncomputable def pickPart (G : PG k q) (Q : Sq k) (P : Pt) (y : Sq k) : Part :=
  if h : ∃ p, p ≠ some P ∧ dem L G Q p y < G.σ.partCnt Q p y then Classical.choose h else none

theorem pickPart_spec (G : PG k q) (Q : Sq k) (P : Pt) (y : Sq k)
    (h : ∃ p, p ≠ some P ∧ dem L G Q p y < G.σ.partCnt Q p y) :
    pickPart L G Q P y ≠ some P ∧
      dem L G Q (pickPart L G Q P y) y < G.σ.partCnt Q (pickPart L G Q P y) y := by
  unfold pickPart; rw [dif_pos h]; exact Classical.choose_spec h

open Classical in
/-- The insertion mode of a stage: cheap when possible. -/
noncomputable def pMode (G : PG k q) (u x : Sq k) (kd : Kind) (y : Sq k) (sp : Pt) : Mode k :=
  if GoodMode L G u x kd y sp .cheap then .cheap
  else .imp (pickPart L G u (dport L u x) y) (pickSur L G u (dport L u x))

section mode
variable {s σ' : ℕ} {σ0 : PState k q} {F0 : ℕ}

/-- The chosen mode is good, and imports never use stock of the port of the hop. -/
theorem pMode_good {G : PG k q} (hL : PLInv L s σ' σ0 F0 G) {u x : Sq k} (hux : u ≠ x)
    {kd : Kind} {y : Sq k} {sp : Pt} (hr : PRoleOK G u x sp kd y)
    (hcap : (∑ z, G.stk u z) + 1 < psz σ0 u (dport L u x)) :
    GoodMode L G u x kd y sp (pMode L G u x kd y sp) ∧
      (kd = .stk → (pMode L G u x kd y sp).ind = 1 → sp ≠ dport L u x) := by
  set P := dport L u x
  by_cases hc : GoodMode L G u x kd y sp .cheap
  · have e : pMode L G u x kd y sp = .cheap := by unfold pMode; rw [if_pos hc]
    rw [e]
    exact ⟨hc, fun _ h => by simp [Mode.ind] at h⟩
  · have e : pMode L G u x kd y sp = .imp (pickPart L G u P y) (pickSur L G u P) := by
      unfold pMode; rw [if_neg hc]
    rw [e]
    have hstk_le : ∀ pt, G.stock u pt y ≤ G.stk u y := fun pt =>
      Finset.single_le_sum (f := fun pt => G.stock u pt y) (fun _ _ => Nat.zero_le _) (mem_univ pt)
    have hroles := hL.roles_le u y
    -- the class is held beyond its demanded stock
    have hsp : kd = .stk → sp ≠ P := by
      intro hk hsP
      apply hc
      subst hk
      obtain ⟨hy, h1⟩ := hr
      rw [hy] at h1 ⊢
      rw [hsP] at h1
      have h2 : G.stock u P x ≤ G.σ.pc u P x := hL.stockIn u x hux
      exact ⟨(show 1 ≤ G.σ.pc u P x by omega), Or.inl ⟨rfl, hsP⟩⟩
    have hmore : G.stock u (dport L u y) y < G.σ.cnt u y := by
      cases kd with
      | sch =>
        obtain ⟨-, h1⟩ := hr
        have := hstk_le (dport L u y); omega
      | stk =>
        obtain ⟨hy, h1⟩ := hr
        subst hy
        have hne := hsp rfl
        have h2 : G.stock u P y + G.stock u sp y ≤ G.stk u y := by
          unfold PG.stk
          rw [← Finset.sum_pair (f := fun pt => G.stock u pt y) (Ne.symm hne)]
          exact Finset.sum_le_sum_of_subset (subset_univ _)
        show G.stock u P y < _
        omega
      | plh =>
        have h1 : 1 ≤ G.free u y := hr
        have := hstk_le (dport L u y); omega
    obtain ⟨p, hp⟩ := surplus_part L hL u y hmore
    have hpP : p ≠ some P := by
      rintro rfl
      apply hc
      have hp' : dem L G u (some P) y < G.σ.pc u P y := hp
      exact ⟨(show 1 ≤ G.σ.pc u P y by omega), Or.inr hp'⟩
    obtain ⟨z, hz⟩ := surplus_port L hL u P hcap
    have h1 := pickPart_spec L G u P y ⟨p, hpP, hp⟩
    exact ⟨⟨h1.1, h1.2, pickSur_spec L G u P ⟨z, hz⟩⟩, fun hk _ => hsp hk⟩

end mode

end SlidingPuzzle.Port
