import SlidingPuzzle.Hub.Interface
import SlidingPuzzle.Hub.RoundWalk
import SlidingPuzzle.Hub.InFlight

/-! # The abstract transport run

From an `IState` (the abstraction of the normalized input board) build the
plan (`exists_rounds`), set aside the reserve matchings, order the remaining
rounds (`exists_good_order`), walk every round (`exists_round_events`), and
resolve every high-level event into operations:

* `serve S D` with `S.2 = D.2`: `hop2 S D D`;
* with `S.1 = D.1`: `hop1 S D D`;
* otherwise, with the hub `h = (S.1, D.2)`: `hop2 h D D` if `h` has class-`D`
  stock, else the bypass `jump D h y` (a free tile `y` of `h`), then `hop1 S h D`;
* `reloc E Z`: `jump E Z y`, or two jumps through the corner `(Z.1, E.2)`.

Roles (scheduled, stock, free, home) are ghost counts; the stock identity
bounds the bypasses by the in-flight maxima. See `PROOF.md` §§3-7. -/
namespace SlidingPuzzle.Hub

/-- Budget of the transport run. -/
def transportBound (n k s : ℕ) : ℕ :=
  10 ^ 7 * (n ^ 2 * s + k ^ 2 * n ^ 2 * (Nat.log 2 n + 1))

/-- Budget of the region tiles left outside their squares. -/
def misplacedBound (n k : ℕ) : ℕ := 1000 * k ^ 2 * n * (Nat.log 2 n + 1)

/-- The abstract run exists, is valid, and is cheap. -/
theorem exists_valid_run {n k s : ℕ} (hd : HDims n k s)
    (hP1 : 64 * k * (Nat.log 2 n + 1) ≤ s) (σ0 : IState k)
    (hF1 : ∀ Q, (∑ y, σ0.cnt Q y) + (if σ0.blank = Q then 1 else 0) = regionSize k s)
    (hF2 : ∀ y, (∑ Q, σ0.cnt Q y) + σ0.corrCount s y = s ^ 2 - (if IsLast y then 1 else 0)) :
    ∃ es : List (REvent k), σ0.Valid s es ∧ σ0.totalCost s es ≤ transportBound n k s ∧
      (σ0.run s es).offCount ≤ misplacedBound n k := by
  sorry

end SlidingPuzzle.Hub
