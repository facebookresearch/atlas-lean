# Markov basis

Let $X$ be a set of cells, possibly infinite, and let $T$ assign to each cell $x$ a finitely
supported exponent vector $T(x) \in \mathbb{N}^{(J)}$, for a set $J$ of parameters. Tables of counts
are finitely supported maps $X \to \mathbb{N}$, moves are finitely supported maps
$X \to \mathbb{Z}$, and the sufficient statistic of a table $a$ is $T(a) = \sum_x a(x)\, T(x)$. A
family of moves $(f_i)_{i \in I}$ is a Markov basis for $T$ when

- each $f_i$ lies in the lattice of moves: $\sum_x f_i(x)\, T(x) = 0$; and
- any two tables of counts $g$ and $g'$ with $T(g) = T(g')$ are joined by a finite sequence of steps
  $\pm f_i$ through tables of nonnegative counts.

## Sources

- P. Diaconis and B. Sturmfels, *Algebraic algorithms for sampling from conditional distributions*, Ann. Statist. 26 (1998), 363–397, Definition (1.5).
