import SlidingPuzzle.Tree.RunTraffic

/-! # The residence bound for the run

The run's ghost lanes carry `(tag, clean)`; forgetting the flag gives exactly the
ghost lanes of the residence theorem. For a good order, the tiles tagged `x` in
the lanes landing at `v` are at most `Nv v x`, the sum of the residence bounds of
these lanes. -/
namespace SlidingPuzzle.Tree
open Finset
open SlidingPuzzle.Hub (Sq Round shiftIn)

variable {k q : ℕ} (L : LaneSys k q)

/-- Forgetting the clean flag of a ghost entry. -/
def gproj (a : GCls k × ℕ) : Sq k × ℕ := (a.1.1, a.2)

theorem ghostRun_toRes (st off : Ln k q → ℕ) (Lst : List (GRec k q)) :
    ∀ g : Ln k q → ℕ → Option (GCls k × ℕ),
      GroupedPipe.ghostRun st off (fun l r => (g l r).map gproj) (Lst.map toRes) =
        fun l r => (GroupedPipe.ghostRun st off g Lst l r).map gproj := by
  induction Lst with
  | nil => intro g; rfl
  | cons a t ih =>
    intro g
    simp only [List.map_cons, GroupedPipe.ghostRun, List.foldl_cons]
    have hstep : GroupedPipe.ghostStep st off (fun l r => (g l r).map gproj) (toRes a) =
        fun l r => (GroupedPipe.ghostStep st off g a l r).map gproj := by
      funext l r
      simp only [GroupedPipe.ghostStep, toRes]
      by_cases hl : l = a.H
      · subst hl
        simp only [Function.update_self]
        unfold shiftIn
        split_ifs <;> rfl
      · simp only [Function.update_of_ne hl]
    rw [hstep]
    exact ih _

theorem gtg_eq_res (s : ℕ) (G : GS k q) (l : Ln k q) (r : ℕ) :
    gtg (gh k s G l r) = (GroupedPipe.ghostRun (lstep s) (loff k s) (fun _ _ => none)
      (G.ins.map toRes) l r).map Prod.fst := by
  have h := ghostRun_toRes (lstep (q := q) s) (loff k s) G.ins (fun _ _ => none)
  simp only [Option.map_none] at h
  rw [h]
  simp only [gtg, gh, Option.map_map]
  rfl

/-- The in-flight bound of a square and tag: the residence bounds of the lanes
landing there. -/
noncomputable def NvOf (N : Ln k q → Sq k → ℕ) (v x : Sq k) : ℕ :=
  ∑ l ∈ univ.filter (fun l : Ln k q => land l = v), N l x

theorem Fcnt_le (s : ℕ) (N : Ln k q → Sq k → ℕ) (Lres : List (GroupedPipe.InsRec (Ln k q) (Sq k)))
    (hres : ∀ m, m ≤ Lres.length → ∀ H x len,
      ((range len).filter fun r =>
        (GroupedPipe.ghostRun (lstep s) (loff k s) (fun _ _ => none) (Lres.take m) H r).map
          Prod.fst = some x).card ≤ N H x)
    (G : GS k q) (hpre : G.ins.map toRes <+: Lres) (v x : Sq k) :
    Fcnt L s G v x ≤ NvOf N v x := by
  unfold Fcnt lcnt NvOf
  rw [← Finset.sum_filter]
  refine sum_le_sum fun l _ => ?_
  have hm : (G.ins.map toRes).length ≤ Lres.length := hpre.length_le
  have e : Lres.take (G.ins.map toRes).length = G.ins.map toRes :=
    (List.prefix_iff_eq_take.1 hpre).symm
  have := hres _ hm l x (llen L s l)
  rw [e] at this
  refine le_trans (le_of_eq ?_) this
  congr 1
  apply filter_congr
  intro r _
  show gtg (gh k s G l r) = some x ↔ _
  rw [gtg_eq_res]

end SlidingPuzzle.Tree
