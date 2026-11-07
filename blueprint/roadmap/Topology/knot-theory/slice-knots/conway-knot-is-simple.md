# The Conway knot polyline is a simple closed curve

Let $K$ be the Conway knot $11n34$,
realized as a closed polyline in $\mathbb{R}^3$ (the braid closure of a 4-strand braid word for
it), and let $N$ be its number of vertices. The periodic piecewise-linear parametrization of $K$,
which traverses each edge in unit time, is injective on the interval $[0, N)$.

Equivalently, the vertices of $K$ are distinct, non-adjacent edges are disjoint, and adjacent
edges meet only at their shared vertex.

## Sources

- https://arxiv.org/abs/1808.02923 Via leanprover/lean-eval@38361be, problem `conway_knot_not_smoothly_slice`.
