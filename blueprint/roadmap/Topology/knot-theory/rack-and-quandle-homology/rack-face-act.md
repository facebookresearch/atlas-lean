# Action face of a tuple in a dihedral quandle

For a natural number $p$, let $R_p$ be the dihedral quandle on $\mathbb{Z}/p$ with operation $a * b = 2b - a$. For a tuple $x = (x_1, \dots, x_{m+1})$ of elements of $\mathbb{Z}/p$ and a position $i \in \{1, \dots, m+1\}$, the action face $d_i^1 x$ is the $m$-tuple obtained by letting $x_i$ act on the entries before it and then omitting the $i$-th entry:

$$d_i^1 x = (x_1 * x_i, \dots, x_{i-1} * x_i, x_{i+1}, \dots, x_{m+1}).$$

It is the second term of each summand of the [rack boundary](rack-boundary.md); the [deletion face](rack-face-delete.md) is the first.

## Sources

- M. Niebrzydowski and J. H. Przytycki, Homology of dihedral quandles, J. Pure Appl. Algebra 213 (2009), 742-755, arXiv:math/0611803, Definition 1.1(i).
