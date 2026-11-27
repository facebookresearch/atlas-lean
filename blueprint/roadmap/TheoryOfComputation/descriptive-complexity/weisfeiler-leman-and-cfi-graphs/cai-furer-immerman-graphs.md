# Cai–Fürer–Immerman graphs

Let $B$ be a finite connected base graph in which every vertex has degree at least two, and $t : E(B) \to \mathbb{F}_2$ a *twist*. The CFI graph $X(B, t)$ replaces every base vertex $v$ of degree $d$ by a *gadget*: vertices $a_{v,e}^0, a_{v,e}^1$ for each edge $e \ni v$ and *middle vertices* $m_{v,S}$ for each even subset $S$ of the edges at $v$, with $m_{v,S}$ adjacent to $a_{v,e}^1$ for $e \in S$ and to $a_{v,e}^0$ for $e \notin S$. For each base edge $e = vw$, the vertices $a_{v,e}^i$ and $a_{w,e}^j$ are joined iff $i \oplus j = t(e)$. As in Cai–Fürer–Immerman, $X(B,t)$ is vertex-colored: the middle vertices of the gadget of $v$ get color $v$ and $a_{v,e}^0, a_{v,e}^1$ get color $(v,e)$, and isomorphisms of CFI graphs preserve colors. The *even* and *odd* CFI graphs over $B$ use twists of total parity $0$ and $1$.

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992, Section 6 (construction of $X(G)$ for a finite, connected graph $G$ every vertex of which has degree at least two).
