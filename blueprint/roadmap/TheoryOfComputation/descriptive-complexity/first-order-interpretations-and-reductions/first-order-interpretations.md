# First-order interpretations

A *first-order interpretation* $I$ of dimension $d$ of a relational vocabulary $\tau$ in a vocabulary $\sigma$ consists of a domain formula $\delta(\bar x)$ in $d$ variables and, for each $R \in \tau$ of arity $r$, a formula $\varphi_R(\bar x_1,\dots,\bar x_r)$ over $\sigma$ with $r$ blocks of $d$ variables. In a $\sigma$-structure $\mathfrak{A}$ it defines the $\tau$-structure $I(\mathfrak{A})$ with universe $\{\bar a \in A^d : \mathfrak{A} \models \delta(\bar a)\}$ and $R^{I(\mathfrak{A})} = \{(\bar a_1,\dots,\bar a_r) : \mathfrak{A} \models \varphi_R(\bar a_1,\dots,\bar a_r)\}$. A *tagged* interpretation takes a disjoint union of several such pieces of possibly different dimensions, with relation formulas for each combination of pieces; a piece of dimension $0$ has a sentence as domain formula and contributes one element when it holds. $I$ is *quantifier-free* if $\delta$ and all $\varphi_R$ are.

## Depends on

- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
