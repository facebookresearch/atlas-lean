# General matching decision problem

The decision problem that accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding, to a triple $(n, E, K)$ of a
natural number $n$, a list $E$ of pairs of natural numbers and a natural number $K$ such that
every pair $(u, v)$ in $E$ has $u < n$, $v < n$ and $u \neq v$, and some sublist $M$ of $E$
(a subsequence, keeping the order of $E$) with no repeated entries and length at least $K$ has
the property that any two different pairs $(u_1, v_1)$ and $(u_2, v_2)$ in $M$ share no
element: $u_1, v_1 \notin \{u_2, v_2\}$. Bitstrings that do not decode are rejected.
