import SlidingPuzzle.Tree.RunDefs

/-! # The inserting squares of a route

`L.nodes u x` lists the squares that insert a tile of class `x` on the way from
`u` to `x`: `u`, `nxt u x`, …, the last square before `x`. They have strictly
decreasing rank, so a route uses each lane at most once. Row hops keep the band
of `u`; column hops happen in the block column of `x`. -/
namespace SlidingPuzzle.Tree
open SlidingPuzzle.Hub (Sq)

variable {k q : ℕ}

/-- The inserting squares, with fuel. -/
def LaneSys.nodesF (L : LaneSys k q) : ℕ → Sq k → Sq k → List (Sq k)
  | 0, _, _ => []
  | f + 1, u, x => if u = x then [] else u :: L.nodesF f (L.nxt u x) x

/-- The inserting squares of the route from `u` to `x`. -/
def LaneSys.nodes (L : LaneSys k q) (u x : Sq k) : List (Sq k) := L.nodesF (L.srank u x) u x

theorem nodes_self (L : LaneSys k q) (x : Sq k) : L.nodes x x = [] := by
  unfold LaneSys.nodes; rw [srank_self]; rfl

theorem nodes_cons (L : LaneSys k q) {u x : Sq k} (h : u ≠ x) : L.nodes u x = u :: L.nodes (L.nxt u x) x := by
  unfold LaneSys.nodes
  rw [srank_nxt h]
  simp only [LaneSys.nodesF, if_neg h]

theorem length_nodes (L : LaneSys k q) (u x : Sq k) : (L.nodes u x).length = L.srank u x := by
  induction hr : L.srank u x generalizing u with
  | zero => rw [srank_eq_zero hr, nodes_self]; rfl
  | succ r ih =>
    have hne : u ≠ x := fun e => by rw [e, srank_self] at hr; omega
    rw [nodes_cons L hne, List.length_cons, ih]
    have := srank_nxt (L := L) hne; omega

/-- Facts about the members of a route. -/
theorem mem_nodes (L : LaneSys k q) {u x w : Sq k} (hw : w ∈ L.nodes u x) :
    w ≠ x ∧ L.srank w x ≤ L.srank u x ∧ (w = u ∨ L.srank w x < L.srank u x) ∧
      ((L.stage w x).1.1 = false → w.1 = u.1) ∧ ((L.stage w x).1.1 = true → w.2 = x.2) ∧
      (u.2 = x.2 → w.2 = x.2) := by
  induction hr : L.srank u x generalizing u with
  | zero => rw [srank_eq_zero hr, nodes_self] at hw; simp at hw
  | succ r ih =>
    have hne : u ≠ x := fun e => by rw [e, srank_self] at hr; omega
    rw [nodes_cons L hne, List.mem_cons] at hw
    have hrn := srank_nxt (L := L) hne
    rcases hw with rfl | hw
    · refine ⟨hne, by omega, Or.inl rfl, fun _ => rfl, ?_, fun h => h⟩
      intro h
      by_contra h2
      simp [LaneSys.stage, h2] at h
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih hw (by omega)
      have hband : (L.stage u x).1.1 = false ∨ u.2 = x.2 := by
        by_cases h2 : u.2 = x.2
        · exact Or.inr h2
        · left; simp [LaneSys.stage, h2]
      refine ⟨a1, by omega, Or.inr (by omega), ?_, a5, ?_⟩
      · intro h
        rw [a4 h]
        by_cases h2 : u.2 = x.2
        · -- a column hop from `u`: then `w` is in the column phase
          exfalso
          have hn2 : (L.nxt u x).2 = x.2 := by
            simp [LaneSys.nxt, LaneSys.stage, h2, land, colLand]
          have := a6 hn2
          have hw2 : (L.stage w x).1.1 = true := by simp [LaneSys.stage, this]
          rw [h] at hw2; cases hw2
        · simp [LaneSys.nxt, LaneSys.stage, h2, land, rowLand]
      · intro h2
        apply a6
        simp [LaneSys.nxt, LaneSys.stage, h2, land, colLand]

theorem nodes_nodup (L : LaneSys k q) (u x : Sq k) : (L.nodes u x).Nodup := by
  induction hr : L.srank u x generalizing u with
  | zero => rw [srank_eq_zero hr, nodes_self]; exact List.nodup_nil
  | succ r ih =>
    have hne : u ≠ x := fun e => by rw [e, srank_self] at hr; omega
    rw [nodes_cons L hne, List.nodup_cons]
    have hrn := srank_nxt (L := L) hne
    refine ⟨fun hm => ?_, ih (L.nxt u x) (by omega)⟩
    have := (mem_nodes L hm).2.1
    omega

/-- The landing square determines the rank, so distinct members use distinct lanes. -/
theorem nodes_lane_inj (L : LaneSys k q) {u x w w' : Sq k} (hw : w ∈ L.nodes u x) (hw' : w' ∈ L.nodes u x)
    (h : (L.stage w x).1 = (L.stage w' x).1) : w = w' := by
  have h1 := srank_nxt (L := L) (mem_nodes L hw).1
  have h2 := srank_nxt (L := L) (mem_nodes L hw').1
  have e : L.nxt w x = L.nxt w' x := by unfold LaneSys.nxt; rw [h]
  have hr : L.srank w x = L.srank w' x := by rw [h1, h2, e]
  -- members of a route are determined by their rank
  induction hr' : L.srank u x generalizing u with
  | zero => rw [srank_eq_zero hr', nodes_self] at hw; simp at hw
  | succ r ih =>
    have hne : u ≠ x := fun e => by rw [e, srank_self] at hr'; omega
    rw [nodes_cons L hne, List.mem_cons] at hw hw'
    have hrn := srank_nxt (L := L) hne
    rcases hw with rfl | hw <;> rcases hw' with rfl | hw'
    · rfl
    · have := (mem_nodes L hw').2.1; omega
    · have := (mem_nodes L hw).2.1; omega
    · exact ih hw hw' (by omega)

/-- The insertion records of the route from `u` to `x`: lane, block distance,
tag. -/
def LaneSys.edgeIns (L : LaneSys k q) (u x : Sq k) : List (Ln k q × ℕ × Sq k) :=
  (L.nodes u x).map fun w =>
    ((L.stage w x).1, LaneSys.pdist (L.stage w x).1.2.t.val (L.stage w x).2.val, x)

end SlidingPuzzle.Tree
