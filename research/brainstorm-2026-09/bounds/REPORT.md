# Lower bounds, literature, and where to aim

I = (OPT − M)/2, the least number of inefficient moves. Scripts: lb.py (admissible bounds on
symmetric boards), climb.py (annealing to maximise them), bfs3.py (exhaustive 3×3), ida4.c
(optimal 15-puzzle solver, IDA* with 5-5-5 additive PDB; reproduces Korf #1, OPT 57).

## Literature
- Demaine–Rudoy, TCS 2018 (arXiv 1707.03146), read in full: NP-hardness via rectilinear
  Steiner tree. Lemma: blank-visited cells are connected; every unchanged visited cell is
  entered ≥ 2 times, so OPT ≥ 2·|visited| − #changed. Conclusion calls the worst case "a
  natural open question": O(n³) above, "Ω(n²) by a simple potential argument".
- Zhong 2023: OPT ≤ M + O(n^2.75); n×2: OPT = inversions + O(n log n).
- Not verified against primary sources: Ratner–Warmuth 1990; Parberry 1995 (5n³+O(n²), one
  snippet says 11n³/3); Parberry 2015 ((8/3)n³ expected); Korf–Schultze 2005 (15-puzzle God's
  number 80); 24-puzzle 152 ≤ G ≤ 205; Takahashi walking/inversion distance.
- No follow-up improving Zhong's exponent found, no worst-case bound on I beyond Θ(n²)
  (no "cited by" search). State of the art: n² ≲ max I ≲ n^(11/4).

## Rigorous lower-bound tools
- Linear conflicts (LIS form): tiles in their goal row that never leave keep their order, so
  ≥ |S_r| − LIS_r leave, each first departure an inefficient vertical move; same for columns.
  I ≥ Σ_r(|S_r| − LIS_r) + Σ_c(|T_c| − LIS_c).
- Inversion distance: a vertical move changes row-major inversions by ≤ n−1 (parity n−1), so
  #vertical moves ≥ ⌈inv/(n−1)⌉; vertical moves = V + 2·(vertical inefficiency).
- Demaine–Rudoy connectivity: only for nearly solved boards (≈ n²/8 at best).

Results: row mirror I ≥ n² − O(n) (bound/n² = 0.88, 0.93, 0.97, 0.98 at n = 10,16,32,64) —
best known worst case. rot180: inversion distance exceeds M by n²−2n−2, so I ≥ n²/2 − O(n)
and God's number ≥ n³ + n² − 2n − 2 (no printed source found). rot90, transpose,
antitranspose: bounds give 0 for n ≥ 10. All tools cap at O(n²) (one departure per tile;
inversion distance ~ n³/2 per axis on boards with M ≈ n³; connectivity counts cells).
Flux arguments fail (cut crossings match M exactly; vertical-only relaxation exact on rot180).
Heuristic: in a region where every tile wants down-right, rotating a loop is exactly half
efficient; efficient circulation needs lanes flowing in opposite directions.

## Exact small boards
3×3 exhaustive (181,440 states): max I = 9 (72 states, e.g. `2 1 3 / 4 5 6 / 8 7 0`, OPT 22,
M 4); mean I = 3.99; God's-number positions (31) have M = 21, I = 5.

| board (* = one swap for parity) | 3×3 OPT/M/I | 4×4 OPT/M/I |
|---|---|---|
| rot180 | 28/20/4 (bound tight) | 78/58/10 (bound 6) |
| rot90 | 14/14/0 | 39/37/1 (4×4 needed the swap) |
| transpose | 28/16/6* (bound 0) | 72/40/16 = n² (bound 0) |
| mirror* | 28/10/9 | unfinished |
| flip* | 30/12/9 | unfinished |

4×4 God's number 80 and max M 60 imply some 4×4 board has I ≥ 10.

## Recursive halving
Length ≈ 2n³ gives I ≈ (2/3)n³ on rot90, n³/2 on rot180 (heuristic): crossing tiles land
anywhere in their goal half and are moved again; a tile travels ≈ 3.4n against Manhattan
≈ (2/3)n; loops move bystanders, about half inefficiently. Additive only if target-aware at
every level (= Zhong's corridors). n×2 case: row-mirror board costs O(n² log n) by solving
pairs of rows as 2×n strips, so its n² bound is nearly tight.

## Where to aim (this agent's view)
- Constant work within 11/4 looked nearly exhausted to this agent (8.45 → 6–7), but it did not
  consider exit-and-restore or conveyor Preparation.
- Exponent: 11/4 balances Transport n³/k against corridor setup k³n². Speculative: hierarchical
  corridor sharing with O(k·n) corridor tiles → n³/k + k·n² → n^(5/2); multi-scale might reach
  n²·polylog. (The structure agent found shared corridors fail at the junction with H_i.)
- Lower bounds: an ω(n²) bound needs genuinely new ideas; not worth investing.
