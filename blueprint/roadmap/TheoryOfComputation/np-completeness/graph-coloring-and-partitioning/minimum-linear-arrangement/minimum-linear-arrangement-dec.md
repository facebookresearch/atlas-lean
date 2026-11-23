# The MINIMUM LINEAR ARRANGEMENT decision problem

It accepts a bitstring $x$ exactly when
$x$ decodes, under the canonical bitstring encoding, to a triple $(n, E, K)$ of a natural number
$n$, a list $E$ of pairs of natural numbers and a natural number $K$ with the following
properties: every entry of $E$ is a pair $(u, v)$ of distinct numbers below $n$, the list $E$ has
no repeated entries and never contains both $(u, v)$ and $(v, u)$, and there is an ordering of
$0, 1, \dots, n-1$ in which, writing $p(v)$ for the position of $v$, the sum of $|p(u) - p(v)|$
over all pairs $(u, v)$ in $E$ is at most $K$. Bitstrings that do not decode are rejected.
