import Mathlib

/-! # Lane systems

A lane system on `k` blocks (of one axis) with `q` offsets. At offset `o` a
*piece* ending at the landing block `t` covers `len o t side` blocks: the blocks
`t+1, …, t+len` (`side = true`, to the right of `t`) or `t-len, …, t-1`
(`side = false`). Pieces of one offset are disjoint and do not cover the landing
block of a nonempty piece. `hop J c` is the next hop of a tile at block `J`
whose target block is `c ≠ J`: the offset of a piece containing `J` and its
landing block, which lies between `J` and `c`. The level `lvl` increases along
hops, so a route has at most `depth` hops. `X o t side` contains every target
block routed through the piece. -/
namespace SlidingPuzzle.Tree

/-- Block `J` lies in the piece of length `l` landing at `t` on `side`. -/
def InPiece (l t : ℕ) (side : Bool) (J : ℕ) : Prop :=
  if side then t < J ∧ J ≤ t + l else J < t ∧ t ≤ J + l

instance (l t : ℕ) (side : Bool) (J : ℕ) : Decidable (InPiece l t side J) := by
  unfold InPiece; split <;> infer_instance

structure LaneSys (k q : ℕ) where
  len : Fin q → Fin k → Bool → ℕ
  X : Fin q → Fin k → Bool → Finset (Fin k)
  hop : Fin k → Fin k → Fin q × Fin k
  lvl : Fin k → Fin k → ℕ
  depth : ℕ
  right_lt : ∀ o t, t.val + len o t true < k
  left_le : ∀ o t, len o t false ≤ t.val
  disj : ∀ o (t t' : Fin k) side side' (J : ℕ), InPiece (len o t side) t side J →
    InPiece (len o t' side') t' side' J → t = t' ∧ side = side'
  avoid : ∀ o (t t' : Fin k) side side', 0 < len o t side →
    ¬ InPiece (len o t' side') t' side' t.val
  hop_in : ∀ J c : Fin k, J ≠ c →
    InPiece (len (hop J c).1 (hop J c).2 (decide (c < J))) (hop J c).2 (decide (c < J)) J.val
  hop_le : ∀ J c : Fin k, J < c → (hop J c).2 ≤ c
  hop_ge : ∀ J c : Fin k, c < J → c ≤ (hop J c).2
  hop_X : ∀ J c : Fin k, J ≠ c → c ∈ X (hop J c).1 (hop J c).2 (decide (c < J))
  lvl_lt : ∀ J c : Fin k, J ≠ c → lvl J c < depth
  lvl_hop : ∀ J c : Fin k, J ≠ c → (hop J c).2 ≠ c → lvl J c < lvl (hop J c).2 c
  sum_len : ∀ t, ∑ o, ∑ side, len o t side ≤ 2 * depth * k
  sum_X : ∀ t, ∑ o, ∑ side, (X o t side).card ≤ 2 * depth * k
  X_le : ∀ o t side, (X o t side).card ≤ len o t side

namespace LaneSys

variable {k q : ℕ} (L : LaneSys k q)

/-- The side of the piece used by a hop from `J` toward `c`. -/
def side (J c : Fin k) : Bool := decide (c < J)

theorem inPiece_lt {l t : ℕ} {side : Bool} {J : ℕ} (h : InPiece l t side J) :
    (side = true ∧ t < J) ∨ (side = false ∧ J < t) := by
  unfold InPiece at h; cases side <;> simp_all

/-- Block distance of `J` from the landing block `t` of its piece, minus one. -/
def pdist (t J : ℕ) : ℕ := Nat.dist J t - 1

theorem pdist_lt {l t : ℕ} {side : Bool} {J : ℕ} (h : InPiece l t side J) : pdist t J < l := by
  unfold pdist Nat.dist; unfold InPiece at h; cases side <;> simp at h <;> omega

theorem hop_ne (J c : Fin k) (h : J ≠ c) : (L.hop J c).2 ≠ J := by
  intro e
  have := L.hop_in J c h
  rw [e] at this
  unfold InPiece at this; split at this <;> omega

/-- The new block is strictly closer to the target. -/
theorem hop_dist (J c : Fin k) (h : J ≠ c) :
    Nat.dist (L.hop J c).2.val c.val < Nat.dist J.val c.val := by
  have hin := L.hop_in J c h
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have := L.hop_le J c hlt
    have hs : decide (c < J) = false := by simp; exact hlt.le
    rw [hs] at hin; unfold InPiece at hin; simp at hin
    have : (L.hop J c).2.val ≤ c.val := this
    unfold Nat.dist; omega
  · have := L.hop_ge J c hlt
    have hs : decide (c < J) = true := by simp; exact hlt
    rw [hs] at hin; unfold InPiece at hin; simp at hin
    have : c.val ≤ (L.hop J c).2.val := this
    unfold Nat.dist; omega

/-- The distance travelled by a hop plus the remaining distance is the old distance. -/
theorem hop_dist_add (J c : Fin k) (h : J ≠ c) :
    Nat.dist J.val (L.hop J c).2.val + Nat.dist (L.hop J c).2.val c.val = Nat.dist J.val c.val := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have := L.hop_le J c hlt
    have hin := L.hop_in J c h
    have hs : decide (c < J) = false := by simp; exact hlt.le
    rw [hs] at hin; unfold InPiece at hin; simp at hin
    have : (L.hop J c).2.val ≤ c.val := this
    unfold Nat.dist; omega
  · have := L.hop_ge J c hlt
    have hin := L.hop_in J c h
    have hs : decide (c < J) = true := by simp; exact hlt
    rw [hs] at hin; unfold InPiece at hin; simp at hin
    have : c.val ≤ (L.hop J c).2.val := this
    unfold Nat.dist; omega

/-- Remaining hops from `J` to `c`, with fuel. -/
def rankF : ℕ → Fin k → Fin k → ℕ
  | 0, _, _ => 0
  | f + 1, J, c => if J = c then 0 else rankF f (L.hop J c).2 c + 1

/-- Number of hops from `J` to `c`. -/
def rank (J c : Fin k) : ℕ := L.rankF k J c

theorem rankF_stable (f : ℕ) (J c : Fin k) (hf : Nat.dist J.val c.val ≤ f) :
    L.rankF (f + 1) J c = L.rankF f J c := by
  induction f generalizing J with
  | zero =>
    have : J = c := Fin.ext (by unfold Nat.dist at hf; omega)
    simp [rankF, this]
  | succ f ih =>
    show (if J = c then 0 else L.rankF (f + 1) (L.hop J c).2 c + 1) =
      (if J = c then 0 else L.rankF f (L.hop J c).2 c + 1)
    split_ifs with h
    · rfl
    · rw [ih _ (by have := L.hop_dist J c h; omega)]

theorem rankF_eq (f : ℕ) (J c : Fin k) (hf : Nat.dist J.val c.val ≤ f) :
    L.rankF f J c = L.rank J c := by
  have hk : Nat.dist J.val c.val ≤ k := by
    have := J.isLt; have := c.isLt; unfold Nat.dist; omega
  have key : ∀ g, f ≤ g → L.rankF g J c = L.rankF f J c := by
    intro g hg
    induction g, hg using Nat.le_induction with
    | base => rfl
    | succ g hg ih => rw [L.rankF_stable g J c (by omega), ih]
  unfold rank
  rcases le_total f k with h | h
  · exact (key k h).symm
  · have key' : ∀ g, k ≤ g → L.rankF g J c = L.rankF k J c := by
      intro g hg
      induction g, hg using Nat.le_induction with
      | base => rfl
      | succ g hg ih => rw [L.rankF_stable g J c (by omega), ih]
    exact key' f h

theorem rank_self (c : Fin k) : L.rank c c = 0 := by
  unfold rank
  cases k with
  | zero => exact c.elim0
  | succ k => simp [rankF]

theorem rank_hop (J c : Fin k) (h : J ≠ c) : L.rank J c = L.rank (L.hop J c).2 c + 1 := by
  have hk : Nat.dist J.val c.val ≤ k := by
    have := J.isLt; have := c.isLt; unfold Nat.dist; omega
  have hpos : 1 ≤ Nat.dist J.val c.val := by
    have : J.val ≠ c.val := fun e => h (Fin.ext e); unfold Nat.dist; omega
  rw [← L.rankF_eq (Nat.dist J.val c.val) J c le_rfl]
  obtain ⟨f, hf⟩ : ∃ f, Nat.dist J.val c.val = f + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hf]
  show (if J = c then 0 else L.rankF f (L.hop J c).2 c + 1) = _
  rw [if_neg h, L.rankF_eq f _ c (by have := L.hop_dist J c h; omega)]

/-- Routes have at most `depth - lvl` hops. -/
theorem rank_le_aux (J c : Fin k) (h : J ≠ c) : L.rank J c + L.lvl J c ≤ L.depth := by
  induction hdist : Nat.dist J.val c.val using Nat.strong_induction_on generalizing J with
  | _ m ih =>
    rw [L.rank_hop J c h]
    by_cases ht : (L.hop J c).2 = c
    · rw [ht, L.rank_self]; have := L.lvl_lt J c h; omega
    · have := ih _ (hdist ▸ L.hop_dist J c h) _ ht rfl
      have := L.lvl_hop J c h ht
      omega

theorem rank_le (J c : Fin k) : L.rank J c ≤ L.depth := by
  by_cases h : J = c
  · rw [h, rank_self]; exact Nat.zero_le _
  · have := L.rank_le_aux J c h; omega

/-- The blocks of a piece. -/
def piece (o : Fin q) (t : Fin k) (side : Bool) : Finset (Fin k) :=
  Finset.univ.filter fun J => InPiece (L.len o t side) t side J.val

theorem card_filter_fin (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun J : Fin k => P J.val).card = ((Finset.range k).filter P).card := by
  apply Finset.card_bij (fun J _ => J.val)
  · intro J hJ; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    simp [J.isLt, hJ]
  · intro a _ b _ h; exact Fin.ext h
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨⟨j, hj.1⟩, by simp [hj.2], rfl⟩

theorem card_piece (o : Fin q) (t : Fin k) (side : Bool) :
    (L.piece o t side).card = L.len o t side := by
  unfold piece
  rw [card_filter_fin]
  cases side
  · have hl := L.left_le o t
    have : (Finset.range k).filter (fun J => InPiece (L.len o t false) t.val false J) =
        Finset.Ico (t.val - L.len o t false) t.val := by
      ext j; simp only [InPiece, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
        Bool.false_eq_true, if_false]
      have := t.isLt; omega
    rw [this, Nat.card_Ico]; omega
  · have hr := L.right_lt o t
    have : (Finset.range k).filter (fun J => InPiece (L.len o t true) t.val true J) =
        Finset.Ioc t.val (t.val + L.len o t true) := by
      ext j; simp only [InPiece, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, if_true]
      omega
    rw [this, Nat.card_Ioc]; omega

/-- The pieces of one offset have at most `k` blocks in all. -/
theorem sum_len_offset (o : Fin q) : ∑ t, ∑ side, L.len o t side ≤ k := by
  classical
  have hdisj : (Set.univ : Set (Fin k × Bool)).PairwiseDisjoint (fun p => L.piece o p.1 p.2) := by
    rintro ⟨t, side⟩ - ⟨t', side'⟩ - hne
    rw [Function.onFun, Finset.disjoint_left]
    intro J h1 h2
    simp only [piece, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨rfl, rfl⟩ := L.disj o t t' side side' J.val h1 h2
    exact hne rfl
  have h := Finset.card_biUnion (s := (Finset.univ : Finset (Fin k × Bool)))
    (t := fun p => L.piece o p.1 p.2) (fun a _ b _ hab => hdisj (Set.mem_univ a) (Set.mem_univ b) hab)
  have hle := Finset.card_le_univ ((Finset.univ : Finset (Fin k × Bool)).biUnion
    fun p => L.piece o p.1 p.2)
  rw [Fintype.card_fin, h] at hle
  rw [← Fintype.sum_prod_type'] 
  simp only [← card_piece]
  exact hle

end LaneSys

end SlidingPuzzle.Tree
