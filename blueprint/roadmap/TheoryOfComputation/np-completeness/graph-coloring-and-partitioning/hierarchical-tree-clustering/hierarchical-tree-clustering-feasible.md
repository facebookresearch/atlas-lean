# Feasible HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) instances

A HIERARCHICAL-TREE CLUSTERING ($\ell_1$ ultrametric fitting) instance with matrix rows $w$ ($n$ rows) and bound $K$ is feasible when some ultrametric $u$ on the points $0, \dots, n-1$ has $\sum_{x < y} |u(x, y) - w(x, y)| \le K$, where $w(x, y)$ is entry $y$ of row $x$ and an entry missing from a short row is read as $0$. For a [well-formed](well-formed.md) instance the matrix is square, symmetric and zero exactly on the diagonal, so no entry is missing.
