# Finite relational structures are determined by their atomic facts

For a relational vocabulary $\sigma$ and $n \in \mathbb{N}$, the $\sigma$-structures with universe $\{0,\dots,n-1\}$ correspond bijectively to truth assignments of the atomic facts $R(a_1,\dots,a_r)$ with $R \in \sigma$ and $a_i < n$. A structure on any $n$-element set, numbered by a bijection with $\{0,\dots,n-1\}$, is isomorphic to the structure of its atomic facts, and satisfaction of a first-order formula is preserved. In particular, for a finite vocabulary $\sigma$ there are exactly $2^{\sum_{R\in\sigma} n^{r(R)}}$ labelled $\sigma$-structures on an $n$-element set.

## Proof sketch

A relational structure is the list of its relations; transport along the numbering bijection.

## Depends on

- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
