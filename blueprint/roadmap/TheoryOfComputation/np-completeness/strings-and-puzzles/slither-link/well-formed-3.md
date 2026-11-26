# Well-formed instances of TRUNCATED HEXAGONAL SLITHER LINK

An instance of TRUNCATED HEXAGONAL SLITHER LINK is well formed when:

- the dodecagon clue grid has $h \ge 1$ rows, and every row has exactly $w$ entries, where $w \ge 1$ is the [width](width-2.md) of the first row;
- the triangle clue grid has $h + 1$ rows, each of exactly $2w + 2$ entries;
- every nonzero [triangle clue entry](triangle-clue.md), at a slot $(x, y)$ with $y \le h$ and $x \le 2w + 1$, sits at a triangle that is a face of the [grid](graph-2.md): all three of its [sides](triangle-sides.md) are edges of the grid.

The face test applies to triangle clues only. Dodecagon clue entries are not restricted: every dodecagon $(c, r)$ with $c < w$ and $r < h$ is a face and may carry any clue. For example, a board with one dodecagon carrying the entry $13$ (clue value $12$) and a triangle clue grid of two rows of four zero entries is well formed.
