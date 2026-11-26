# Directed graph isomorphism as a decision problem

The decision problem accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a triple $(n, E_1, E_2)$
of a natural number $n$ and two lists $E_1$ and $E_2$ of pairs of natural numbers for which
there is a bijection $f$ of $\{0, \dots, n - 1\}$ such that for all $a, b < n$, $(a, b) \in E_1$
if and only if $(f(a), f(b)) \in E_2$. Bitstrings that do not decode to such a triple are
rejected.

Pairs in $E_1$ or $E_2$ with an entry at least $n$ play no role.
