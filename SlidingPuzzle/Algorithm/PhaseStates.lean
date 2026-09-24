import SlidingPuzzle.Algorithm.BoardCounts
import SlidingPuzzle.Algorithm.TransportPostcondition
import SlidingPuzzle.Bridge.Reachability

/-! Contracts for the four global states used by the partition algorithm.

The size equation `n = k^4` is deliberately kept out of these definitions:
it belongs to the transition and counting arguments that use the contracts. -/
namespace SlidingPuzzle.Partition

variable {n k : ℕ} [NeZero n]

/-- The final reservoir contains a representative of every other target group. -/
def LastRepresentatives (hk : 2 ≤ k) (B : Board n) : Prop :=
  ∀ j : GroupIndex k, j ≠ lastGroup k hk →
    0 < reservoirCount B (lastGroup k hk) j

/-- Every nonblank label in a square belongs to that square's target group. -/
def SquaresSorted (B : Board n) : Prop :=
  ∀ (i : GroupIndex k) (c : Cell n), square i c → (B c).val ≠ 0 →
    B c ∈ targetGroup i

/-- The preparation endpoint, also the transport input. -/
structure Prepared (hk : 2 ≤ k) (B : Board n) : Prop where
  reachable : Reachable B
  clear : Clear (k := k) B
  representatives : LastRepresentatives hk B

/-- The transport endpoint, also the arrangement input. -/
structure Transported (hk : 2 ≤ k) (B : Board n) : Prop where
  reachable : Reachable B
  clear : Clear (k := k) B
  sorted : ReservoirSorted (k := k) B
  blank_last : reservoir (lastGroup k hk) (blank B)

/-- The input contract for the finishing phase. -/
structure Arranged (hk : 2 ≤ k) (B : Board n) : Prop where
  reachable : Reachable B
  sorted : SquaresSorted (k := k) B
  blank_last : square (lastGroup k hk) (blank B)

/-- A prepared board has its blank in one of the reservoirs. -/
theorem Prepared.blank_in_reservoir {B : Board n} {hk : 2 ≤ k}
    (hB : Prepared hk B) (hn : n = k^4) :
    ∃ i : GroupIndex k, reservoir i (blank B) :=
  SlidingPuzzle.Partition.blank_in_reservoir hk hn B hB.clear

/-- A preparation construction supplies reachability automatically through its path. -/
theorem Prepared.of_path {B C : Board n} {hk : 2 ≤ k}
    (hB : Reachable B) (p : Path B C) (hclear : Clear (k := k) C)
    (hrep : LastRepresentatives hk C) : Prepared hk C := by
  obtain ⟨q⟩ := hB
  exact ⟨⟨q.append p⟩,hclear,hrep⟩

/-- A sorted clear endpoint has the required blank position; it is not a new
blank-routing assumption imposed on the transport construction. -/
theorem Transported.of_path {B C : Board n} {hk : 2 ≤ k}
    (hn : n=k^4) (hB : Reachable B) (p : Path B C)
    (hclear : Clear (k := k) C) (hsorted : ReservoirSorted (k := k) C) :
    Transported hk C := by
  obtain ⟨q⟩ := hB
  exact ⟨⟨q.append p⟩,hclear,hsorted,
    clear_reservoirSorted_blank_in_lastReservoir hk hn C hclear hsorted⟩

/-- To use the count abstraction, a transport implementation must still supply
an actual path and a clear endpoint whose own matrix is sorted. -/
theorem Transported.of_count_endpoint {B C : Board n} {hk : 2 ≤ k}
    (hn : n=k^4) (hB : Prepared hk B) (p : Path B C)
    (hclear : Clear (k := k) C)
    (hmass : TransportCounts.offdiagMass (boardMatrix hk C)=0) : Transported hk C :=
  Transported.of_path hn hB.reachable p hclear
    ((reservoirSorted_iff_boardMatrix_offdiagMass_eq_zero hk hn C).mpr hmass)

/-- Square sorting implies reservoir sorting because reservoirs lie within squares. -/
theorem Arranged.reservoirSorted {B : Board n} {hk : 2 ≤ k}
    (hB : Arranged hk B) : ReservoirSorted (k := k) B := by
  intro i c hc hnonzero
  exact hB.sorted i c (reservoir_subset_square hc) hnonzero

/-- Arranged boards retain the parity invariant of the target. -/
theorem Arranged.parity {B : Board n} {hk : 2 ≤ k}
    (hB : Arranged hk B) :
    parityInvariant B = colorSign (blank (target n)) :=
  reachable_parityInvariant B hB.reachable

/-- Any path from a reachable input carries the global parity/reachability
condition into an endpoint with the required square and blank properties. -/
theorem Arranged.of_path {B C : Board n} {hk : 2 ≤ k}
    (hB : Reachable B) (p : Path B C) (hsorted : SquaresSorted (k := k) C)
    (hblank : square (lastGroup k hk) (blank C)) : Arranged hk C := by
  obtain ⟨q⟩ := hB
  exact ⟨⟨q.append p⟩, hsorted, hblank⟩

/-- With the global parity criterion available, the reachability field of an
arranged state is exactly the target parity condition. -/
theorem arranged_iff_parity (hk : 2 ≤ k) (hn2 : 2 ≤ n) (B : Board n) :
    Arranged hk B ↔
      SquaresSorted (k := k) B ∧
        square (lastGroup k hk) (blank B) ∧
          parityInvariant B = colorSign (blank (target n)) := by
  constructor
  · intro hB
    exact ⟨hB.sorted, hB.blank_last, hB.parity⟩
  · rintro ⟨hsorted, hblank, hparity⟩
    exact ⟨reachable_of_parityInvariant hn2 B hparity, hsorted, hblank⟩

/-- The target board itself satisfies the finishing-phase contract. -/
theorem target_arranged (hk : 2 ≤ k) (hn : n = k^4) :
    Arranged hk (target n) := by
  refine ⟨⟨Path.nil _⟩, ?_, ?_⟩
  · intro i c hc hnonzero
    exact (mem_targetGroup i (target n c)).mpr ⟨hnonzero, by simp [position] at hc ⊢; exact hc⟩
  · exact (square_target_blank hk hn (lastGroup k hk)).mpr rfl

/-- Square sorting is equivalently expressed by placing every target group in
its own current square. -/
theorem squaresSorted_iff_positions (hk : 2 ≤ k) (hn : n = k^4) (B : Board n) :
    SquaresSorted (k := k) B ↔
      ∀ (i : GroupIndex k) (t : Tile n), t ∈ targetGroup i →
        square i (position B t) := by
  constructor
  · intro hsorted i t ht
    obtain ⟨j, hj⟩ := square_covers hk hn (position B t)
    have hnonzero : (B (position B t)).val ≠ 0 := by
      simpa [position] using (mem_targetGroup i t).mp ht |>.1
    have hplaced : B (position B t) ∈ targetGroup j :=
      hsorted j (position B t) hj hnonzero
    have htj : t ∈ targetGroup j := by
      simpa [position] using hplaced
    have hij : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (targetGroups_disjoint hk hne)) ht htj
    simpa [hij] using hj
  · intro hpositions i c hc hnonzero
    obtain ⟨j, hj⟩ := targetGroups_cover hk hn (B c) hnonzero
    have hcurrent : square j (position B (B c)) := hpositions j (B c) hj
    have hjc : square j c := by simpa [position] using hcurrent
    have hij : i = j := square_unique hk hc hjc
    simpa [hij] using hj

end SlidingPuzzle.Partition
