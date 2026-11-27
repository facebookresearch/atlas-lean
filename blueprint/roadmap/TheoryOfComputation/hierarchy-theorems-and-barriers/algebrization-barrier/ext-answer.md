# Answer bits of the algebraic extension oracle

Let $n$ be a natural number, let $p$ be a
monic irreducible polynomial of degree $n + 1$ over $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$, let
$F = \mathbb{F}_2[X]/(p)$ with $\alpha$ the class of $X$, let $B$ be a function from bitstrings to
booleans, and let $\tilde B_n$ be the multilinear extension over $F$ of the restriction of $B$ to
inputs of length $n$. Given a list $(e_0, e_1, \ldots)$ of bitstrings and an index $j$ with
$0 \le j \le n$, let $e_{i,k} \in \{0, 1\}$ be the bit of $e_i$ at position $k$, counting from
$0$, where a missing list entry or a missing bit counts as $0$, and let $x \in F^n$ be the point
with coordinates $x_i = \sum_{k=0}^{n} e_{i,k} \alpha^k$ for $i < n$. The answer bit is true
exactly when the coefficient of $\alpha^j$ in $\tilde B_n(x)$, written in the basis
$1, \alpha, \dots, \alpha^n$ of $F$ over $\mathbb{F}_2$, equals $1$.

The index $j$ ranges over $0, \dots, n$ only: an out-of-range index must be rejected by the
caller, not reduced modulo $n + 1$.
