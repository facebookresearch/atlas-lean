# One step of the moves chain

Let $X$ be a set of cells, possibly infinite, and let $T$ assign to each cell $x$ a finitely
supported exponent vector $T(x) \in \mathbb{N}^{(J)}$, for a set $J$ of parameters. Tables of counts
are finitely supported maps $X \to \mathbb{N}$, moves are finitely supported maps
$X \to \mathbb{Z}$, and the sufficient statistic of a table $a$ is $T(a) = \sum_x a(x)\, T(x)$. For
a family of moves $(f_i)_{i \in I}$ and tables of counts $g$ and $h$, one step of the moves chain
leads from $g$ to $h$ when $h = g + \varepsilon f_i$ for some $i \in I$ and some
$\varepsilon \in \{1, -1\}$; both $g$ and $h$ have nonnegative counts.

## Sources

- P. Diaconis and B. Sturmfels, *Algebraic algorithms for sampling from conditional distributions*, Ann. Statist. 26 (1998), 363–397, condition (1.5b) with a single move.
