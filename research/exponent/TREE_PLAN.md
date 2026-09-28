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

## Status (2026-09-28, branch `tree`)

Proved in Lean, no `sorry` (`SlidingPuzzle/Tree/`): lane systems and the
`b`-ary instance (`Hier.sys`), layout and all board operations (`simulate_run`),
residence with per-lane step, the whole abstract run with placeholders, stock
identity and the rank bound (`exists_valid_run`), preload (`exists_preload`),
and the algorithm on side `k*s` (`exists_tree_solution`, bound `treeBound`).

Remaining: (1) bound `treeBound` for `L = Hier.sys b h`, `q = h*b`, `k = b^h`
(sums of `laneCells`, `needAt`, `resv`; hypotheses `hfit`, capacity `hcap`,
`hcA`, `hcB`, and `TDims`: `b` even, `8 k^2 q < n`-type conditions);
(2) general sides via the Parberry prefix (as `Hub/AsympBound`);
(3) choose `b ≈ n^(1/(2h+1))` and derive `OPT ≤ M + C_h n^((5h+3)/(2h+1)) log n`,
then `5/2 + ε`. Files are not yet imported by `SlidingPuzzle.lean`.
