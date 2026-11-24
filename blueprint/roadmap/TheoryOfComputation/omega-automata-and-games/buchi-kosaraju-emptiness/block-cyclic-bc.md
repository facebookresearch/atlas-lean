# Block Cyclic BC

Assume that equality on `V` is decidable.

Costed Boolean cyclic test: the same `Bool` as `blockCyclicB`, plus the
cost. One length test always; the self-loop scan runs only when the
block has length `< 2` (short-circuit `||`).
