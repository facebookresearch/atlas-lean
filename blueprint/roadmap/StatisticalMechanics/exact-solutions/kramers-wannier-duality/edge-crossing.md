# Edge crossing between a graph and its dual

Let $V$ be a finite set and let $G_p$ (primal) and $G_d$ (dual) be simple graphs on $V$. An edge crossing from $G_p$ to $G_d$ is a bijection $\psi$ of the set of unordered pairs of elements of $V$ such that

- $\psi(e)$ is an edge of $G_d$ for every edge $e$ of $G_p$;
- $\psi(C)$ is an [even subgraph](is-even-subgraph.md) of $G_d$ for every [cut set](cut-space.md) $C$ of $G_p$;
- $\psi^{-1}(F)$ is a cut set of $G_p$ for every [even subgraph](even-subgraphs.md) $F$ of $G_d$.
