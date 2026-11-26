# Ordered finite structures with built-in numerical predicates

Fix a finite relational vocabulary $\sigma$. An **ordered $\sigma$-structure** is a $\sigma$-structure with universe $\{0,1,\dots,n-1\}$, $n\ge2$, interpreted together with the built-in numerical relations $\le$, $\mathrm{BIT}(i,j)$ (the $j$-th bit of $i$ is $1$), and constants $0$, $1$, $\max=n-1$. A **query** is an isomorphism-closed class of such structures, and its encoded language consists of the binary encodings (universe size in unary followed by the truth tables of the relations). A logic $\mathcal{L}$ **captures** a complexity class $\mathcal{C}$ on ordered structures if the queries definable by $\mathcal{L}$-sentences are exactly those whose encoded languages lie in $\mathcal{C}$.

## Depends on

- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)
- [Finite ordered graphs](../immerman-vardi-theorem/ordered-graph.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999.
- Leonid Libkin, "Elements of Finite Model Theory", Springer, 2004.
