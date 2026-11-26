# First-order reductions between queries on ordered structures

Consider finite relational structures whose universe is $\{0, \ldots, n-1\}$ with $n \ge 2$, equipped with the numeric predicates $\le$, $\mathrm{BIT}$ and constants $0, 1, \max$. A query is an isomorphism-closed class of such structures over a vocabulary $L$. A $k$-dimensional full-tuple first-order interpretation from $L$ to $L'$ ($k \ge 1$) maps a structure $\mathcal{A}$ of size $n$ to the $L'$-structure $I(\mathcal{A})$ whose universe is the set of $k$-tuples, ordered lexicographically and identified with $\{0, \ldots, n^k - 1\}$, and in which each relation $R'$ of arity $r$ is defined by a first-order $L$-formula $\varphi_{R'}(\bar x_1, \ldots, \bar x_r)$ in $kr$ variables. A query $K$ first-order reduces to $K'$ ($K \le_{\mathrm{fo}} K'$) if some such interpretation satisfies $\mathcal{A} \in K \iff I(\mathcal{A}) \in K'$ for every structure $\mathcal{A}$.

## Depends on

- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)
- [Finite ordered graphs](../immerman-vardi-theorem/ordered-graph.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Graduate Texts in Computer Science, Springer, 1999.
- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
