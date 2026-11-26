# TRUNCATED HEXAGONAL SLITHER LINK is NP-complete

The TRUNCATED HEXAGONAL SLITHER LINK decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: integers $w, h \ge 1$ and two explicitly listed clue grids for the truncated hexagonal grid with $h$ rows of $w$ dodecagons: one entry for each of the $wh$ dodecagons ($h$ rows of $w$ entries) and one entry for each hex vertex ($h + 1$ rows of $2w + 2$ entries), the latter for the triangles between the dodecagons. Each entry is either "no clue" or a clue value, and triangle clues appear only at triangles that are faces of the grid. The input therefore has size proportional to $wh$, as with the unary dimensions of Section 4 of the source. Question: is there a cycle $C$ in the grid such that every clue face has exactly as many of its sides in $C$ as its clue value?

## Sources

- J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information Processing 20(3) (2012), 709-712, [doi:10.2197/ipsjjip.20.709](https://doi.org/10.2197/ipsjjip.20.709), Theorem 1.
