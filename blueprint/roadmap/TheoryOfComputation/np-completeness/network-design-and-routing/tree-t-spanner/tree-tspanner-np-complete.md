# TREE t-SPANNER is NP-complete for every fixed t ≥ 4

For every natural number $t$ with $4 \le t$, the [TREE t-SPANNER decision problem](tree-tspanner-dec.md) with parameter $t$ lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph $G = (V, E)$. Question: does $G$ have a tree $t$-spanner, i.e. a spanning tree $T$ of $G$ with $d_T(u, v) \le t \cdot d_G(u, v)$ for all $u, v \in V$?

## Sources

- L. Cai and D. G. Corneil, "Tree spanners", SIAM Journal on Discrete Mathematics 8 (1995), 359-387, doi:10.1137/S0895480192237403.
- I. Papoutsakis, "Tree spanners of bounded degree graphs", arXiv:1503.06822 (Section 1: the attribution of NP-completeness for each $t \ge 4$ to Cai and Corneil, and Definition 1 of a tree $t$-spanner).
