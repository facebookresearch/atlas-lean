# Feasible instances of TRUNCATED HEXAGONAL SLITHER LINK

An instance of TRUNCATED HEXAGONAL SLITHER LINK is feasible when some cycle of the [grid](graph-2.md) (a closed walk of positive length with no repeated edge, whose only repeated vertex is its start) satisfies every nonzero clue entry at the enumerated candidate positions, where $h$ is the number of rows of the dodecagon clue grid and $w$ the [width](width-2.md) of its first row:

- for every $r < h$ and $c < w$ whose [dodecagon clue entry](dodecagon-clue.md) is $v + 1$, exactly $v$ of the twelve [sides](dodecagon-sides.md) of dodecagon $(c, r)$ are edges of the cycle;
- for every $y \le h$ and $x \le 2w + 1$ whose [triangle clue entry](triangle-clue.md) is $v + 1$, exactly $v$ of the three candidate [sides](triangle-sides.md) of the triangle slot at hex vertex $(x, y)$ are edges of the cycle.

The triangle test applies to every nonzero entry at such a slot, whether or not the triangle there is a face of the grid; that clues sit only at faces is a condition of [well-formedness](well-formed-3.md). Feasibility does not include well-formedness; the decision problem requires both.
