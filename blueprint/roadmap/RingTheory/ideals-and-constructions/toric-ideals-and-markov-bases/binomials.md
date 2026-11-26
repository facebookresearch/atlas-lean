# Binomials of a toric model

Let $X$ be a set of cells, possibly infinite, and let $T$ assign to each cell $x$ a finitely
supported exponent vector $T(x) \in \mathbb{N}^{(J)}$, for a set $J$ of parameters. Tables of counts
are finitely supported maps $X \to \mathbb{N}$, moves are finitely supported maps
$X \to \mathbb{Z}$, and the sufficient statistic of a table $a$ is $T(a) = \sum_x a(x)\, T(x)$. For
a field $k$, $k[X]$ is the polynomial ring in the variables $x \in X$, $x^a = \prod_x x^{a(x)}$ for
a table $a$, and the toric ideal $I_T$ is the kernel of the monomial map
$k[X] \to k[t_j : j \in J]$, $x \mapsto t^{T(x)}$. The binomials of $T$ are the polynomials
$x^a - x^b$ with $T(a) = T(b)$. Up to a monomial factor they are the differences $x^{f^+} - x^{f^-}$
for moves $f$ with $\sum_x f(x)\, T(x) = 0$, since
$x^a - x^b = x^{a \wedge b}\,(x^{a - a \wedge b} - x^{b - a \wedge b})$.

## Sources

- P. Diaconis and B. Sturmfels, *Algebraic algorithms for sampling from conditional distributions*, Ann. Statist. 26 (1998), 363–397, equation (3.1).
