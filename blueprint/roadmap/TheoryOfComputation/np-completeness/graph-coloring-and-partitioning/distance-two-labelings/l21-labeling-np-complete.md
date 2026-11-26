# L(2,1)-LABELING is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph with at least one vertex on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a positive integer $K$, decide whether the vertices can be labeled with $\{0, \dots, K\}$ so that adjacent vertices get labels at least $2$ apart and vertices at distance two get different labels.

## Sources

- J. R. Griggs and R. K. Yeh, "Labelling graphs with a condition at distance 2", SIAM Journal on Discrete Mathematics 5 (1992), 586-595, doi:10.1137/0405048.
- J. Fiala, T. Kloks and J. Kratochvíl, "Fixed-parameter complexity of λ-labelings", Discrete Applied Mathematics 113 (2001), 59-72, doi:10.1016/S0166-218X(00)00387-5.
