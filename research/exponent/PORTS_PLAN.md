# Ports: gateway hops that do not pay `s`

Goal: remove the factor `h` from the per-tile transport cost, taking the error from
`n^(5/2) (ln n)^(3/2)` to `n^(5/2) ln n` (and close to `n^(5/2) √(ln n)` for all
practical `n`). Model: [`model/ports_model.py`](model/ports_model.py) on top of
[`model/tree_model.py`](model/tree_model.py), which evaluates `treeBound`
(`Tree/Transport.lean`) with the budget inputs of `FineLog.polynomial_budget_log`.

## Diagnosis

The error is about `h · √λ · n^(5/2)`, and at a fixed grid `k ≈ √(n/16λ)` every
term linear in `h` comes from the hops: `hopK ≈ 20s` per hop, `2h` hops per tile
(`RunMain.runCost`, `OpHopR.simulate_hopR`). Of the `20s`, about `17s` is the
insertion (`OpInsert.insert_by_cycle`): a jump and a three-cycle in the source
square's box, which fetch a tile of the right class from an arbitrary region cell.
The other `3s` walk the blank along the landing strip from an arbitrary cell of the
landing square.

At a source this is unavoidable, since the tile could be anywhere in the square. At a gateway
it is not. The stock tile arrived earlier as the head of a lane that dropped at the
landing cell, and the next hop inserts at the same edge of the same block. For a tile
landing at `L` (near end of its child) from the west, the next row hop inserts at the
edge of `v` farthest from `t'`, which is again the west edge (`Basic.rowPos`). Drop
cell and insertion cell are `O(q + k)` apart. The region abstraction (`IState.cnt`, a bag
per square) forgets this and pays `s`.

Removing only the `λ` slack (derandomized residence) does not change the order: with
`λ = O(1)` the best branching is `b ≈ e³` and `h^(3/2)√b` is still of order
`(ln n)^(3/2)`.

## Design

Split every square's region into the main region and four *ports*: small boxes
of side `σ ≈ √(6qs + 30λkq)` at the lane ends. `W` and `N` share the top-left corner
(row lanes use the top `q` rows, column lanes the left `q` columns), `E` sits at
the top-right and `S` at the bottom-left.

- `IState.cnt : Sq → Sq → ℕ` becomes counts per (square, part), part ∈ {main, W, E, N, S}.
- A hop's head drops into the port of its landing side.
- A **gateway hop** (inserter `≠` source) inserts from the port on the same side, at cost
  `O(σ + q + k)`. The blank also starts from a known cell (the previous hop's insertion
  cell, at the same edge), so the `3s` strip walk shrinks too.
- A **source hop** inserts from main, at `O(s)` as now. Its three-cycle can at the
  same time move one home tile from a port into the vacated main cell (eviction).
  A square sends and receives one tile per round, so the ports do not fill with
  home tiles.
- A **turn** (row phase done, `v.2 = x.2`) moves a stock tile from the `W`/`E` port to the
  `N`/`S` port. `W → N` costs `O(q + k)`, and `E → N/S` costs `O(s)`, once per tile.
- Stock, free and placeholder tiles live in ports. For fixed `(v, x)` the arrival
  side and the departure side agree (`v` is the `L` or the `U` of the child
  containing `x`), so the stock identity and `B ≤ inflight + dArr + 1` hold per port.
  The preload fills the ports' reserves.

Per tile: one `O(s)` source insertion, at most one `O(s)` turn, and `2h` hops of
`O(σ + q + k)`, instead of `2h` hops of `20s`.

## Expected effect (model, error / n^(5/2), optimal depth and branching per `n`)

| `n` | now `/(ln n)^(3/2)` | ports `/(ln n)^(3/2)` | ports `/√(ln n)` |
| --- | --- | --- | --- |
| `2²³` | 77 | 44 | 701 |
| `2⁴⁰` | 63 | 25 | 688 |
| `2⁶⁰` | 60 | 17 | 702 |
| `2¹⁰⁰` | 55 | 10 | 723 |
| `2²⁰⁰` | 50 | 5.6 | 780 |

(These are model values of `treeBound`, not the certified constants. The
certified `245` corresponds to about `2 × 1.3 × 77`: inefficient moves count
twice, and the `(48h+142)` linearization loses about 1.3.)

Asymptotically, the terms still linear in `h` are the placeholders
(`ΣB ≤ (2h+1) Σ(inflight + 1)`, each costing `O(n)`, i.e. `(2h+1)·kq/s` per `k²s³`) and
the lane-crossing part `20k(q+2)` of `hopK`. The crossing is monotone toward the target,
so it telescopes to `O(kq)` per tile once charged by distance. Balancing the placeholders with
`s ≳ k·h·q` gives `O(n^(5/2) ln n)`. Reaching `√(ln n)` would need a placeholder bound
that does not grow with `h` as well.

## Lean work (milestones)

1. Layout: port boxes, `key` with parts, region counts per part (`Layout`,
   `LayoutFacts`, `Abs`).
2. Operations: `hopR`/`hopC` from a port (new insertion by a three-cycle in the port box),
   source hop with eviction, turn (`OpHopR`, `OpHopC`, `OpInsert`, a new `OpTurn`).
3. Run: roles per part in the ghost state, stock identity per port, preload into
   ports (`RunGhost`, `RunServe`, `RunInv`, `RunLocal`, `RunRank`, `Preload`).
4. Accounting: a new `runCost` with `hopK_src`, `hopK_gw`, and FineLog/LamLog with a
   depth rule chosen for the new balance.
