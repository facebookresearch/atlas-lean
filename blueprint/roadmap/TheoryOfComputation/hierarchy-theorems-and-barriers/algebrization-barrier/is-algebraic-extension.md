# Algebraic extension oracles

Let $B$ and $O$ be oracles, that is, functions from
bitstrings to booleans. Then $O$ is an algebraic extension of $B$ when there are polynomials
$\pi_0, \pi_1, \pi_2, \ldots$ over $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$, each $\pi_n$ monic and
irreducible of degree $n + 1$, with the following two properties, where $F_n$ is the field
$\mathbb{F}_2[X]/(\pi_n)$, $\alpha_n$ is the class of $X$ in $F_n$, and $\tilde B_n$ is the
multilinear extension over $F_n$ of the restriction of $B$ to inputs of length $n$. First, the
map sending a bitstring $u$ to the coefficient bitstring of $\pi_{|u|}$ with parameter $|u|$
(whose bits say which of the coefficients of $X^0, \dots, X^{|u|+1}$ equal $1$) is
polynomial-time computable. Second, let $y$ be a bitstring. If $y$ decodes, under the canonical
bitstring encoding of triples, to a triple $(u, (e_0, \dots, e_{m-1}), j)$ of a bitstring $u$, a
list of bitstrings and a natural number $j$ such that, writing $n = |u|$, we have $m = n$, every
$e_i$ has length $n + 1$ and $j \le n$, then $O(y)$ is true exactly when the coefficient of
$\alpha_n^j$ in $\tilde B_n(x)$, written in the basis $1, \alpha_n, \dots, \alpha_n^n$ of $F_n$
over $\mathbb{F}_2$, equals $1$. Here $x \in F_n^n$ is the point with coordinates
$x_i = \sum_{k=0}^{n} e_{i,k} \alpha_n^k$, where $e_{i,k} \in \{0, 1\}$ is the bit of $e_i$ at
position $k$, counting from $0$. Otherwise, in particular when $y$ does not decode, $O(y)$ is
false.

Every malformed query is answered false, so an oracle machine cannot route around the algebraic
structure through invalid encodings, and an out-of-range $j$ does not wrap around to
coordinate $0$.
