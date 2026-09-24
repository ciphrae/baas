# Reused Zhong formalization sources

These source files were copied on 2026-09-13 from the existing local project
`/home/rhea/math/zhong/Zhong`, using dependency closures rooted at `Zhong.Extremal`,
`Zhong.Algorithm.Strip2` and `Zhong.Algorithm.JumpAll`.
The original files identify their authors as "Zhong formalisation contributors"
and declare Apache 2.0 licensing. Original headers and source text are preserved.
The source project contains no standalone LICENSE file; LICENSE-2.0.txt here
contains the standard Apache 2.0 text (copied from the installed mathlib license).
SHA-256 hashes in SOURCE_HASHES.json identify the exact copied files.

These modules retain the `Zhong` namespace. `SlidingPuzzle` remains the project's
public puzzle interface. Bridge theorems must prove compatibility of moves,
reachable orbits, distance and statistics before using these imported results.
In particular, Zhong's out-of-bounds moves are identity operations and must be
omitted when converting words to the project's strictly legal paths.

The old Phase I/availability/transport modules and diagnosis notes are deliberately
excluded. Algorithm phases in this workspace follow the paper and the current
formalization plan. An inspected comment in the old Build module incorrectly
called the paper's vertical-strip column a typo: the paper already states
`b_i*k^3+j`, matching the intended partition. That module was not retained.
