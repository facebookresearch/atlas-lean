# Rack boundary map

For a natural number $p$, the dihedral quandle $R_p$ is $\mathbb{Z}/p$ with the operation $a * b = 2b - a$. The rack chain group $C_m(R_p)$ is the free abelian group on the $m$-tuples $(x_1, \dots, x_m)$ of elements of $\mathbb{Z}/p$. The rack boundary $\partial : C_{m+1}(R_p) \to C_m(R_p)$ is

$$\partial(x_1, \dots, x_{m+1}) = \sum_{i=2}^{m+1} (-1)^i \bigl( (x_1, \dots, \widehat{x_i}, \dots, x_{m+1}) - (x_1 * x_i, \dots, x_{i-1} * x_i, x_{i+1}, \dots, x_{m+1}) \bigr),$$

where $\widehat{x_i}$ means that $x_i$ is omitted.

## Sources

- M. Niebrzydowski and J. H. Przytycki, Homology of dihedral quandles, J. Pure Appl. Algebra 213 (2009), 742-755, arXiv:math/0611803, Definition 1.1(i).
