# Gaifman graphs, distance and neighborhoods

The *Gaifman graph* of a relational structure $\mathfrak{A}$ has universe $A$ and an edge between distinct $a, b$ whenever they occur together in some tuple of some relation of $\mathfrak{A}$. Its path metric $d$ takes values in $\mathbb{N} \cup \{\infty\}$. For a tuple $\bar a$ and $r \in \mathbb{N}$, the *ball* $B_r(\bar a)$ is the set of elements at distance at most $r$ from some entry of $\bar a$, and the *$r$-neighborhood* $N_r(\bar a)$ is the substructure induced on $B_r(\bar a)$ with $\bar a$ distinguished. Two pointed structures have *isomorphic $r$-neighborhoods*, $N_r(\bar a) \cong N_r(\bar b)$, if some isomorphism of the induced substructures maps $\bar a$ to $\bar b$.

## Depends on

- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
