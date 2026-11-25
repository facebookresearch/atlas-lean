# MINIMUM t-SPANNER is NP-complete for every fixed t ≥ 2

For every natural number $t \ge 2$, the following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a connected simple graph $G$ on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a positive integer $K$, decide whether $G$ has a spanning subgraph $H$ with at most $K$ edges such that $d_H(u, v) \le t \cdot d_G(u, v)$ for all vertices $u$ and $v$.

## Sources

- D. Peleg and A. A. Schäffer, "Graph spanners", Journal of Graph Theory 13(1) (1989), 99-116, doi:10.1002/jgt.3190130114 (t = 2).
- L. Cai, "NP-completeness of minimum spanner problems", Discrete Applied Mathematics 48(2) (1994), 187-194, doi:10.1016/0166-218X(94)90073-6 (every fixed t ≥ 2); both restated in R. Ahmed, G. Bodwin, F. Darabi Sahneh, K. Hamm, M. J. Latifi Jebelli, S. Kobourov and R. Spence, "Graph spanners: A tutorial review", Computer Science Review 37 (2020), 100253, doi:10.1016/j.cosrev.2020.100253 (arXiv:1909.03152), Section 3.1.
