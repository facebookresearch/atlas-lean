# Feasible instances of GENERALIZED SHISEN-SHO

An instance of GENERALIZED SHISEN-SHO is feasible when all tiles can be removed: there is a list of pairs of integer points, removed in order, such that

- the points of all pairs, taken in order, are a rearrangement of the [cells](cells.md) of the board, so every cell occurs exactly once;
- the two points of each pair have the same [label](label.md);
- the two points of each pair are [connectable](connectable.md) when the occupied points are exactly the cells that do not occur in the earlier pairs.

Only remaining board cells are occupied: every point outside the $R \times C$ rectangle, and every cell already removed, is free, and the bends of a connection range over all of $\mathbb{Z} \times \mathbb{Z}$. Feasibility does not include well-formedness; the decision problem requires both.
