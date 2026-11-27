# Monomial map of a toric model

Let $X$ be a set of cells, possibly infinite, and let $T$ assign to each cell $x$ a finitely
supported exponent vector $T(x) \in \mathbb{N}^{(J)}$, for a set $J$ of parameters. Tables of counts
are finitely supported maps $X \to \mathbb{N}$, moves are finitely supported maps
$X \to \mathbb{Z}$, and the sufficient statistic of a table $a$ is $T(a) = \sum_x a(x)\, T(x)$. For
a field $k$, the monomial map of $T$ is the homomorphism of $k$-algebras
$\varphi_T \colon k[X] \to k[t_j : j \in J]$ from the polynomial ring in the variables $x \in X$
that sends each variable $x$ to the monomial $t^{T(x)}$.

## Sources

- P. Diaconis and B. Sturmfels, *Algebraic algorithms for sampling from conditional distributions*, Ann. Statist. 26 (1998), 363–397, Section 3.1.
