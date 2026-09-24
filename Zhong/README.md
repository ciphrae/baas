# Zhong library

A word-level model of the sliding puzzle from an earlier formalization attempt
(`../Zhong`): rectangular boards `Zhong.Board n m`, operation words over
`Dir`, and their permutation action. Only the parts used by `SlidingPuzzle`
are kept, and several files were modified during cleanup.

It supplies
- the solvability criterion (`Reachable`, `Alternating`, `Glue`),
- orbit statistics of Manhattan distance (`Uniform`, `Expectation`, `Extremal`),
- move words for placements, strips and jumps (`Algorithm/`), used by the
  Parberry solver and the jump constructions.

`SlidingPuzzle/Bridge/` translates words into legal `SlidingPuzzle.Path`s.
Out-of-bounds moves act as the identity in this library and are removed when
translating.
