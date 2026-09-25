import SlidingPuzzle.OrbitParity
import SlidingPuzzle.Algorithm.Transport.Postcondition

/-! The states between the four phases: `Prepared`, `Transported`, `Arranged`.

The size assumptions `Dims n k` are deliberately kept out of these definitions:
it belongs to the transition and counting arguments that use these states. -/
namespace SlidingPuzzle.Partition

variable {n k : ℕ} [NeZero n]

/-- The final reservoir contains a representative of every other target group. -/
def LastRepresentatives (hk : Dims n k) (B : Board n) : Prop :=
  ∀ j : GroupIndex k, j ≠ lastGroup k hk →
    0 < reservoirCount B (lastGroup k hk) j

/-- Every nonblank label in a square belongs to that square's target group. -/
def SquaresSorted (B : Board n) : Prop :=
  ∀ (i : GroupIndex k) (c : Cell n), square i c → (B c).val ≠ 0 →
    B c ∈ targetGroup i

/-- The preparation endpoint, also the transport input. -/
structure Prepared (hk : Dims n k) (B : Board n) : Prop where
  reachable : Reachable B
  clear : Clear (k := k) B
  representatives : LastRepresentatives hk B

/-- The transport endpoint, also the arrangement input. -/
structure Transported (hk : Dims n k) (B : Board n) : Prop where
  reachable : Reachable B
  clear : Clear (k := k) B
  sorted : ReservoirSorted (k := k) B
  blank_last : reservoir (lastGroup k hk) (blank B)

/-- The state before Finish: every tile lies in its own square. -/
structure Arranged (hk : Dims n k) (B : Board n) : Prop where
  reachable : Reachable B
  sorted : SquaresSorted (k := k) B
  blank_last : square (lastGroup k hk) (blank B)

/-- A prepared board has its blank in one of the reservoirs. -/
theorem Prepared.blank_in_reservoir {B : Board n} {hk : Dims n k}
    (hB : Prepared hk B) :
    ∃ i : GroupIndex k, reservoir i (blank B) :=
  SlidingPuzzle.Partition.blank_in_reservoir hk B hB.clear

/-- A preparation construction supplies reachability automatically through its path. -/
theorem Prepared.of_path {B C : Board n} {hk : Dims n k}
    (hB : Reachable B) (p : Path B C) (hclear : Clear (k := k) C)
    (hrep : LastRepresentatives hk C) : Prepared hk C := by
  obtain ⟨q⟩ := hB
  exact ⟨⟨q.append p⟩,hclear,hrep⟩

/-- A sorted clear endpoint has the required blank position; it is not a new
blank-routing assumption imposed on the transport construction. -/
theorem Transported.of_path {B C : Board n} {hk : Dims n k} (hB : Reachable B) (p : Path B C)
    (hclear : Clear (k := k) C) (hsorted : ReservoirSorted (k := k) C) :
    Transported hk C := by
  obtain ⟨q⟩ := hB
  exact ⟨⟨q.append p⟩,hclear,hsorted,
    clear_reservoirSorted_blank_in_lastReservoir hk C hclear hsorted⟩

/-- A clear endpoint reached from a prepared board, whose count matrix has no
off-diagonal mass, is transported. -/
theorem Transported.of_count_endpoint {B C : Board n} {hk : Dims n k} (hB : Prepared hk B) (p : Path B C)
    (hclear : Clear (k := k) C)
    (hmass : TransportCounts.offdiagMass (boardMatrix hk C)=0) : Transported hk C :=
  Transported.of_path hB.reachable p hclear
    ((reservoirSorted_iff_boardMatrix_offdiagMass_eq_zero hk C).mpr hmass)

/-- Square sorting implies reservoir sorting because reservoirs lie within squares. -/
theorem Arranged.reservoirSorted {B : Board n} {hk : Dims n k}
    (hB : Arranged hk B) : ReservoirSorted (k := k) B := by
  intro i c hc hnonzero
  exact hB.sorted i c (reservoir_subset_square hc) hnonzero

/-- Arranged boards retain the parity invariant of the target. -/
theorem Arranged.parity {B : Board n} {hk : Dims n k}
    (hB : Arranged hk B) :
    parityInvariant B = colorSign (blank (target n)) :=
  reachable_parityInvariant B hB.reachable

/-- Any path from a reachable input carries the global parity/reachability
condition into an endpoint with the required square and blank properties. -/
theorem Arranged.of_path {B C : Board n} {hk : Dims n k}
    (hB : Reachable B) (p : Path B C) (hsorted : SquaresSorted (k := k) C)
    (hblank : square (lastGroup k hk) (blank C)) : Arranged hk C := by
  obtain ⟨q⟩ := hB
  exact ⟨⟨q.append p⟩, hsorted, hblank⟩

end SlidingPuzzle.Partition
