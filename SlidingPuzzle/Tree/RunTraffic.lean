import SlidingPuzzle.Tree.RunRank

/-! # Traffic of a round

The records of a round: every lane gets at most `k` insertions (row lanes only
serve sources of their band, column lanes only destinations of their block
column, and a route uses a lane at most once), at most one per tag, and only
tags of its support `Xs`. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq Round ind)

variable {k q : ℕ} (L : LaneSys k q)

/-- Tags carried by a lane. -/
def Xs (l : Ln k q) : Finset (Sq k) :=
  if l.1 then univ.filter fun x => x.2 = l.2.b ∧ x.1 ∈ L.X l.2.o l.2.t l.2.side
  else univ.filter fun x => x.2 ∈ L.X l.2.o l.2.t l.2.side

theorem card_Xs_le (l : Ln k q) : (Xs L l).card ≤ k * blen L l.2 := by
  unfold Xs blen
  split_ifs
  · calc (univ.filter fun x : Sq k => x.2 = l.2.b ∧ x.1 ∈ L.X l.2.o l.2.t l.2.side).card
        ≤ ((L.X l.2.o l.2.t l.2.side) ×ˢ ({l.2.b} : Finset (Fin k))).card := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          exact Finset.mem_product.2 ⟨hx.2, Finset.mem_singleton.2 hx.1⟩
      _ = (L.X l.2.o l.2.t l.2.side).card := by simp
      _ ≤ L.len l.2.o l.2.t l.2.side := L.X_le _ _ _
      _ ≤ k * L.len l.2.o l.2.t l.2.side := Nat.le_mul_of_pos_left _ (by
          have := l.2.b.isLt; omega)
  · calc (univ.filter fun x : Sq k => x.2 ∈ L.X l.2.o l.2.t l.2.side).card
        ≤ ((univ : Finset (Fin k)) ×ˢ L.X l.2.o l.2.t l.2.side).card := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          simp [hx]
      _ = k * (L.X l.2.o l.2.t l.2.side).card := by simp
      _ ≤ k * L.len l.2.o l.2.t l.2.side := Nat.mul_le_mul_left _ (L.X_le _ _ _)

/-- The record of the stage of `w` toward `x`. -/
def stRec (w x : Sq k) : Ln k q × ℕ × Sq k :=
  ((L.stage w x).1, LaneSys.pdist (L.stage w x).1.2.t.val (L.stage w x).2.val, x)

theorem stRec_supp {w x : Sq k} (h : w ≠ x) :
    (stRec L w x).2.1 < blen L (stRec L w x).1.2 ∧ (stRec L w x).2.2 ∈ Xs L (stRec L w x).1 := by
  refine ⟨LaneSys.pdist_lt (stage_in h), ?_⟩
  unfold stRec Xs LaneSys.stage
  by_cases h1 : w.2 = x.2
  · have h2 : w.1 ≠ x.1 := fun e => h (Prod.ext e h1)
    simp only [h1, ne_eq, not_true_eq_false, if_false, if_true, mem_filter, mem_univ, true_and]
    exact L.hop_X _ _ h2
  · simp only [h1, ne_eq, not_false_eq_true, if_true, Bool.false_eq_true, if_false, mem_filter,
      mem_univ, true_and]
    exact L.hop_X _ _ h1

theorem edgeIns_eq (u x : Sq k) : L.edgeIns u x = (L.nodes u x).map fun w => stRec L w x := rfl

theorem mem_roundIns {r : Round k} {p : Ln k q × ℕ × Sq k} (hp : p ∈ roundIns L r) :
    ∃ S w, r.real S ∧ w ∈ L.nodes S (r.perm S) ∧ p = stRec L w (r.perm S) := by
  unfold roundIns at hp
  obtain ⟨S, hS, hp⟩ := List.mem_flatMap.1 hp
  rw [edgeIns_eq] at hp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
  exact ⟨S, w, by simpa using hS, hw, rfl⟩

theorem roundIns_supp (r : Round k) (p : Ln k q × ℕ × Sq k) (hp : p ∈ roundIns L r) :
    p.2.1 < blen L p.1.2 ∧ p.2.2 ∈ Xs L p.1 := by
  obtain ⟨S, w, -, hw, rfl⟩ := mem_roundIns L hp
  exact stRec_supp L (mem_nodes L hw).1

/-- A route uses a lane at most once. -/
theorem countP_edge_lane (u x : Sq k) (H : Ln k q) :
    (L.edgeIns u x).countP (fun p => decide (p.1 = H)) ≤ 1 := by
  rw [edgeIns_eq, List.countP_map]
  rw [List.countP_eq_length_filter]
  have hnd : ((L.nodes u x).filter fun w => decide ((stRec L w x).1 = H)).Nodup :=
    (nodes_nodup L u x).filter _
  by_contra hc
  push Not at hc
  have e : ((fun p : Ln k q × ℕ × Sq k => decide (p.1 = H)) ∘ fun w => stRec L w x) =
      fun w => decide ((stRec L w x).1 = H) := rfl
  rw [e] at hc
  rcases hl : (L.nodes u x).filter (fun w => decide ((stRec L w x).1 = H)) with _ | ⟨a, _ | ⟨b, t⟩⟩
  · rw [hl] at hc; simp at hc
  · rw [hl] at hc; simp at hc
  · rw [hl] at hnd
    have hab : a ≠ b := fun e => by simp [e] at hnd
    have ha : a ∈ (L.nodes u x).filter (fun w => decide ((stRec L w x).1 = H)) := by
      rw [hl]; simp
    have hb : b ∈ (L.nodes u x).filter (fun w => decide ((stRec L w x).1 = H)) := by
      rw [hl]; simp
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    exact hab (nodes_lane_inj L ha.1 hb.1 (by simp only [stRec] at ha hb; rw [ha.2, hb.2]))

/-- A route using lane `H`: row lanes lie in the source's band, column lanes in
the destination's block column. -/
theorem edge_lane_pos {S D : Sq k} {H : Ln k q}
    (h : 0 < (L.edgeIns S D).countP (fun p => decide (p.1 = H))) :
    (H.1 = false → H.2.b = S.1) ∧ (H.1 = true → H.2.b = D.2) := by
  rw [edgeIns_eq, List.countP_pos_iff] at h
  obtain ⟨p, hp, hpH⟩ := h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
  have hpH' := of_decide_eq_true hpH
  simp only [stRec] at hpH'
  subst hpH'
  have hm := mem_nodes L hw
  constructor
  · intro h1
    rw [← hm.2.2.2.1 h1]
    by_cases h2 : w.2 = D.2
    · simp [LaneSys.stage, h2] at h1
    · simp [LaneSys.stage, h2]
  · intro h1
    have e := hm.2.2.2.2.1 h1
    simp [LaneSys.stage, e]

theorem countP_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (p : β → Bool)
    (P : α → Prop) [DecidablePred P] (h1 : ∀ a, (f a).countP p ≤ 1)
    (h2 : ∀ a, 0 < (f a).countP p → P a) :
    (l.flatMap f).countP p ≤ l.countP (fun a => decide (P a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.countP_append, List.countP_cons]
    by_cases ha : P a
    · have := h1 a; simp only [ha, decide_true, if_true]; omega
    · have : (f a).countP p = 0 := by by_contra hc; exact ha (h2 a (Nat.pos_of_ne_zero hc))
      simp only [ha, decide_false, Bool.false_eq_true, if_false]; omega

/-- At most `k` insertions per lane and round. -/
theorem roundIns_batch (r : Round k) (H : Ln k q) :
    (roundIns L r).countP (fun p => decide (p.1 = H)) ≤ k := by
  classical
  unfold roundIns
  set realL := (Finset.univ.filter fun S => r.real S).toList
  have hnd : realL.Nodup := Finset.nodup_toList _
  have key : ∀ P : Sq k → Prop, [DecidablePred P] → (∀ S, 0 < (L.edgeIns S (r.perm S)).countP
      (fun p => decide (p.1 = H)) → P S) → (univ.filter P).card ≤ k →
      (realL.flatMap fun S => L.edgeIns S (r.perm S)).countP (fun p => decide (p.1 = H)) ≤ k := by
    intro P _ hP hk
    refine (countP_flatMap_le realL _ _ P (fun S => countP_edge_lane L S _ H) hP).trans ?_
    rw [List.countP_eq_length_filter]
    have : (realL.filter fun S => decide (P S)).Nodup := hnd.filter _
    refine le_trans ?_ hk
    rw [← List.toFinset_card_of_nodup this]
    apply card_le_card
    intro S hS
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hS
    simp [hS.2]
  cases hH : H.1
  · apply key (fun S => S.1 = H.2.b)
    · intro S hS; exact ((edge_lane_pos L hS).1 hH).symm
    · have : (univ.filter fun S : Sq k => S.1 = H.2.b) = {H.2.b} ×ˢ univ := by
        ext S; simp [Prod.ext_iff, eq_comm]
      rw [this]; simp
  · apply key (fun S => (r.perm S).2 = H.2.b)
    · intro S hS; exact ((edge_lane_pos L hS).2 hH).symm
    · have : (univ.filter fun S : Sq k => (r.perm S).2 = H.2.b) =
          (univ ×ˢ {H.2.b}).map r.perm.symm.toEmbedding := by
        ext S
        simp only [mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.symm_symm, mem_product,
          mem_singleton]
      rw [this, card_map]; simp

/-- At most one insertion of a tag per lane and round. -/
theorem roundIns_class (r : Round k) (H : Ln k q) (x : Sq k) :
    ∑ d ∈ range k, (roundIns L r).countP (fun p => decide (p = (H, d, x))) ≤ 1 := by
  classical
  have h1 : ∑ d ∈ range k, (roundIns L r).countP (fun p => decide (p = (H, d, x))) ≤
      (roundIns L r).countP (fun p => decide (p.1 = H ∧ p.2.2 = x)) := by
    induction (roundIns L r) with
    | nil => simp
    | cons p l ih =>
      simp only [List.countP_cons, sum_add_distrib]
      have : ∑ d ∈ range k, (if p = (H, d, x) then 1 else 0) ≤
          if p.1 = H ∧ p.2.2 = x then 1 else 0 := by
        by_cases hp : p.1 = H ∧ p.2.2 = x
        · rw [if_pos hp]
          calc (∑ d ∈ range k, if p = (H, d, x) then 1 else 0)
              ≤ ∑ d ∈ range k, (if d = p.2.1 then 1 else 0) := sum_le_sum fun d _ => by
                split_ifs with h1 h2 <;> first | omega | (exfalso; exact h2 (by rw [h1]))
            _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> omega
        · rw [if_neg hp]
          apply le_of_eq
          apply Finset.sum_eq_zero
          intro d _
          rw [if_neg]
          rintro rfl
          exact hp ⟨rfl, rfl⟩
      simp only [decide_eq_true_eq] at ih this ⊢
      omega
  refine h1.trans ?_
  unfold roundIns
  set realL := (Finset.univ.filter fun S => r.real S).toList
  have hnd : realL.Nodup := Finset.nodup_toList _
  refine (countP_flatMap_le realL _ _ (fun S => r.perm S = x) ?_ ?_).trans ?_
  · intro S
    refine le_trans (List.countP_mono_left fun p _ h => ?_) (countP_edge_lane L S (r.perm S) H)
    simp only [decide_eq_true_eq] at h ⊢; exact h.1
  · intro S hS
    rw [edgeIns_eq, List.countP_pos_iff] at hS
    obtain ⟨p, hp, hpx⟩ := hS
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hp
    have hpx' := of_decide_eq_true hpx
    exact hpx'.2
  · rw [List.countP_eq_length_filter]
    have : (realL.filter fun S => decide (r.perm S = x)).Nodup := hnd.filter _
    rw [← List.toFinset_card_of_nodup this]
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ha hb
    exact r.perm.injective (ha.2.trans hb.2.symm)

end SlidingPuzzle.Tree
