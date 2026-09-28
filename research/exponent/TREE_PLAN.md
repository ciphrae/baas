# Tree lanes: OPT ≤ M + O_h(n^(5/2 + 1/(4h+2)))

Plan for the Lean development in `SlidingPuzzle/Tree/`: the grouped-corridor
idea of `BELOW_EIGHT_THIRDS.md` / `HIERARCHY_CONDITIONAL.md`, made concrete
enough to formalize. Constants and logarithms are irrelevant here; only the
exponent matters, so every estimate may be crude.

## Parameters

`b` even, `h ≥ 1`, `k = b^h` (even), `s = n/k`, `q = h·b` lane offsets per
band (even). Squares, classes, `sqOf`, `classOf`, reservoirs (offsets `≥ k`),
`HDims n k s` and Cleanup/Finish are reused from `Hub`. Lanes use only the
offsets `< q ≤ k`; offsets in `[q, k)` are ordinary region cells.

## Lane system (one per axis, the same combinatorics)

Offset `o = (ℓ, i)`, `ℓ < h`, `i < b`. At level `ℓ` a parent interval has
`b·m` blocks, `m = b^(h-ℓ-1)`, and its child `i` is `[L, U]`,
`L = base + i·m`, `U = L + m - 1`. Offset `o` carries, inside each parent,
the *left piece* `[base, L)` landing at `L` and the *right piece*
`(U, base + bm)` landing at `U`. Blocks of `[L, U]` are not covered at offset
`o`; the landing blocks' cells are region cells (landing strips).

Abstractly (`LaneSys k q`): `len o t side` (blocks), `cover o J` (the piece
covering block `J` at offset `o`), `hop J c = (o, t)` for `J ≠ c`, and a class
support `X o t side ⊆ Fin k`, with

* pieces of one offset are disjoint and avoid their landing blocks;
* `hop J c` uses a piece containing `J`; `t` lies between `J` and `c`, closer
  to `c`; `c ∈ X` of that piece; routes (iterated hops) have `≤ h` hops;
* for every `t`: `Σ_{o,side} len o t side ≤ 4k` and `Σ |X o t side| ≤ 4k`.

A tile at `(i, J)` with class `(a, c)` hops along row lanes of band `i` until
column `c`, then along column lanes of block column `c` until band `a`. The next
hop from a square `v` for a class `x` depends on `(v, x)` only.

## Layout

Row lane `(band, o, t, side)`: row `band·s + o`, columns as a `Hub` row half
toward block `t`, truncated to `len` blocks. Column lane `(col, o, t, side)`:
column `col·s + o`, rows with offsets `≥ q`, as a `Hub` column half toward band
`t`, crossing row groups of `q` rows by jumps of odd length `q + 1`. The region
of a square is every cell of it that is not a lane cell.

## Operations

`hop L J y`: the blank goes from the landing square along lane `L` to the
source block `J`, which inserts a class-`y` tile at the affine position of
distance `d`; the head drops into the landing square. Cost
`O(s + k + q·(bands crossed)) + junk steps`. `jump E Z y` as in `Hub`.

## Run

No set-aside rounds. **Preload**: before planning, three-cycles put
`R_v` home tiles into every region `v` (`52n` each, charged twice against the
original Manhattan distance). Initial home tiles are *free*; all initial lane
contents are junk.

A round serves each real edge `S → D` by its route `S = v0 → … → vm = D`,
executed backwards (last hop first). The inserter of hop `j` is `v(j-1)`: the
source sends a scheduled tile; a gateway sends a clean stock tile of class `D`
if it has one, else a free tile as a **placeholder**, tagged `D`. Every
planned insertion happens, so the insertion records per round are a fixed
function of the matching, and the residence bound applies.

Arrivals: a tagged-`x` head at `v ≠ x` becomes clean stock if its class is
`x`, else free (a *dirty arrival*); at `v = x` it is home or free; an untagged
(junk) head becomes free unless home.

Identity at serve boundaries, for `v ≠ x`:
`stock(v,x) + inflight(v,x) + dArr(v,x) = B(v,x)` (placeholders of `v` for
`x`). A placeholder happens only at stock zero, so
`B(v,x) ≤ inflight_max(v,x) + dArr(v,x) + 1`. Dirty arrivals return free
tiles to `v`, so the free tiles `v` needs are at most
`Σ_x (inflight_max(v,x) + 1) + dummies(v) + 2`: a deterministic geometric
bound (lanes landing at `v`), which defines `R_v`. Globally, with
`rank(v,x)` = hops left, `dArr` at rank `r` is at most `B` at rank `r+1`, so
`Σ B ≤ 2h · Σ_{v,x} (inflight_max + 1)`.

## Totals

`O_h(n³/k + k·q·n² + n·k³·log n)`: hops `n²·h·(s + qk)`, relocations and
Finish `n³/k`, junk and placeholders `n·(qkn + ΣB)`, preload `n·ΣR_v`,
cleanup `n·(lane cells + ΣR + ΣB)`. With `b ≈ n^(1/(2h+1))`:
`n^((5h+3)/(2h+1))`, hence `n^(5/2+ε)`.

## Status (2026-09-29, branch `tree`)

Complete, no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound` only:
`SlidingPuzzle.Tree.tree_exponent`: for every `ε > 0` there are `C, N` with
`OPT(B) ≤ M(B) + C n^(5/2+ε)` for all reachable boards with `n ≥ N`.

Pipeline: lane systems and `Hier.sys` (`Hier`), layout and board operations,
residence, the abstract run, preload, the algorithm on side `k*s`
(`exists_tree_solution`, bound `treeBound`, `Transport`); then
`AsympAccounting` (lane inventories, reserve totals), `FineAccounting`
(`treeBound ≤ 50 (h+3) k² s³` once `8kq ≤ s`, `16kλ ≤ s`, `2048hk ≤ s`), `ReserveAccounting`
(per-square `needAt`), `Feasibility` (event conditions; `2λ ≤ hb` for `b ≥ 256` and
`n ≤ (2b)^(2h+2)`), `AsympBound` (Parberry prefix to side `k*(n/k)`), `GridChoice`
(depth for a given `ε`), `Final` (`hfit_of_grid`; `optimalLength_le_lanes` for any lane
system with `8k²q ≤ n`, `256h ≤ q ≤ k`, `2λ ≤ q`), `HierMix` (the hierarchy with
branching `B ℓ` at level `ℓ`: `k = ∏ B ℓ`, `q = ∑ B ℓ`), `MixGrid` (branching `b + 2` at
the first `j` levels and `b` below; `b` the largest even with `8h b^(2h+1) ≤ n`, `j` the
largest with `8qk² ≤ n`, so the next `j` fails and `k` is within `(b+2)/b` of the ideal;
`tree_uniform_approximation_explicit`, `tree_uniform_approximation`, `tree_exponent`), and
`MixLog` (depth choice).

Constants: `OPT ≤ M + 102 (h+3) √(8h) n^(5/2+1/(4h+2))` for `n ≥ 8h·256^(2h+1)`.
The leading terms per `k²s³` are hops `40h`, local three-cycles of the run `45`,
preload `≈ 51`, cleanup `≈ 29`, Finish `2.5`, stock `1.5h`; with `s = 8h·b·k` the
lane-proportional terms are about `6h + 73`, and `B0 = 8h` is close to optimal
for the balance `(A + B'/B0)·B0^(h/(2h+1))`. The factor `√(8h)` bounds
`(8h)^(h/(2h+1))`, and `1.012 ≥ (1 + 2/256)^(3/2)` covers the rounding of `k`.
(History: `10^5 (h+1)` accounting, grid `b^(2h+2) ≍ n` with exponent `5/2 + 1/(2h+2)`,
then `160(2h+3) b^(2h+1) ≤ n` with `C_h ≈ 6.4·10^7 (h+1)(2h+3) 2^h`, then a uniform
even `b ≥ max(256, 16h)` with `120 (h+3) √(8h)`: the rounding loss `(1 + 2/b)^h` of a
uniform grid forced `b ≥ 16h`, and with it `(ln n / ln ln n)²` in the depth choice.)

Depth choice (`MixLog`): the largest `h` with `mixN h = 8h·256^(2h+1) ≤ n` has
`n < mixN (h+1) ≤ 176^(4h+2)`, so `n^(1/(4h+2)) ≤ 176`, and `ln n ≥ 11h + 5.5`; with
`(h+3)² h ≤ 5 (h+1/2)³` this gives `OPT ≤ M + 3200 n^(5/2) (ln n)^(3/2)` for `n ≥ 8·256³`
(`tree_log_approximation_explicit`). Asymptotically the coefficient is about `125`.

Statistics (`Stats`): `tree_average_optimal_length` and `tree_gods_number`, the mean
optimal length `(2/3)n³ + O(n^(5/2+ε))` and God's number `n³ + O(n^(5/2+ε))` for
every `ε > 0`, and `tree_log_average_optimal_length`, `tree_log_gods_number` with error
`O(n^(5/2) (ln n)^(3/2))`, via the generic reduction `Hub.AsympStats`.
