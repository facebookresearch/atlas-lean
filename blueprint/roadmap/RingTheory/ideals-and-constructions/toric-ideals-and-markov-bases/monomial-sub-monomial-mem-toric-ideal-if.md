# A binomial lies in the toric ideal iff its exponents have the same statistic

Let $X$ be a set of cells, possibly infinite, and let $T$ assign to each cell $x$ a finitely
supported exponent vector $T(x) \in \mathbb{N}^{(J)}$, for a set $J$ of parameters. Tables of counts
are finitely supported maps $X \to \mathbb{N}$, moves are finitely supported maps
$X \to \mathbb{Z}$, and the sufficient statistic of a table $a$ is $T(a) = \sum_x a(x)\, T(x)$. For
a field $k$, $k[X]$ is the polynomial ring in the variables $x \in X$, $x^a = \prod_x x^{a(x)}$ for
a table $a$, and the toric ideal $I_T$ is the kernel of the monomial map
$k[X] \to k[t_j : j \in J]$, $x \mapsto t^{T(x)}$. For all tables $a$ and $b$, the binomial
$x^a - x^b$ lies in $I_T$ if and only if $T(a) = T(b)$.

## Sources

- P. Diaconis and B. Sturmfels, *Algebraic algorithms for sampling from conditional distributions*, Ann. Statist. 26 (1998), 363–397, Section 3.1, the observation before Theorem 3.1.
