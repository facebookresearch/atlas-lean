# OV-hardness of distinguishing diameter 2 from 3

There is a reduction from Orthogonal Vectors with $N$ vectors of dimension $d$ to sparse graphs with $O(Nd)$ edges whose diameter is $3$ if an orthogonal pair exists and $2$ otherwise. Hence an algorithm distinguishing diameter $2$ from $3$ in time $m^{2-\varepsilon}$ on $m$-edge graphs decides OV in time $N^{2-\varepsilon/2}\mathrm{poly}(d)$ and refutes SETH; in particular no $(3/2-\varepsilon)$-approximation of the diameter runs in time $m^{2-\varepsilon}$ under SETH.

## Proof sketch

Vertices for the vectors of each side, for the coordinates, and two hub vertices; vectors connect to coordinates where they have a $1$, and hubs connect everything except that vector pairs only meet through coordinates. Two vectors on opposite sides are at distance $2$ iff they share a coordinate, otherwise at distance $3$.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Proof depends on

- [Williams: split-and-list transfer from orthogonal vectors to SAT](../exponential-sat-algorithms/orthogonal-vectors-to-sat-transfer.md)

## Sources

- Liam Roditty and Virginia Vassilevska Williams, "Fast Approximation Algorithms for the Diameter and Radius of Sparse Graphs", Proceedings of the Forty-Fifth Annual ACM Symposium on Theory of Computing, 2013, Section 4, Theorem 9.
