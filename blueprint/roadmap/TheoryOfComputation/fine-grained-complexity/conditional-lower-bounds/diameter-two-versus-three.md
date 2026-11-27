# OV-hardness of distinguishing diameter 2 from 3

There is a reduction from Orthogonal Vectors with $N$ vectors of dimension $d$ to sparse graphs with $O(Nd)$ edges whose diameter is $3$ if an orthogonal pair exists and $2$ otherwise. Hence an algorithm distinguishing diameter $2$ from $3$ in time $m^{2-\varepsilon}$ on $m$-edge graphs decides OV in time $N^{2-\varepsilon}\mathrm{poly}(d)$ and refutes SETH; in particular no $(3/2-\varepsilon)$-approximation of the diameter runs in time $m^{2-\varepsilon}$ under SETH.

## Proof sketch

Take a vertex for each vector $a\in A$ and $b\in B$, a vertex for each coordinate $i\in[d]$, and two hubs $t_A,t_B$. Join $a$ to $t_A$ and to the coordinates $i$ with $a_i=1$, join $b$ to $t_B$ and to the coordinates with $b_i=1$, join $t_A$ to $t_B$, and join every coordinate to both hubs. All pairs other than $(a,b)$ with $a\in A$, $b\in B$ are at distance at most $2$ through a hub, and $d(a,b)=2$ iff $a$ and $b$ share a coordinate equal to $1$, otherwise $d(a,b)=3$ (via $t_A t_B$). Roditty and Vassilevska Williams give the same construction directly from CNF-SAT, with half-assignments for vectors and clauses for coordinates.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Proof depends on

- [Williams: split-and-list transfer from orthogonal vectors to SAT](../exponential-sat-algorithms/orthogonal-vectors-to-sat-transfer.md)

## Sources

- Liam Roditty and Virginia Vassilevska Williams, "Fast Approximation Algorithms for the Diameter and Radius of Sparse Graphs", Proceedings of the Forty-Fifth Annual ACM Symposium on Theory of Computing, 2013, Theorem 4 and its proof (reduction from CNF-SAT).
