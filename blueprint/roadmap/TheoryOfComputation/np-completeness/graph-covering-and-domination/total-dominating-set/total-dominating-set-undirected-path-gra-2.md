# TOTAL DOMINATING SET for undirected path graphs is NP-complete

The TOTAL DOMINATING SET for undirected path graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: an undirected path graph `G = (V, E)` with no isolated vertices, that is, the vertex intersection graph of a family of paths in an undirected tree, and a positive integer `K`. Question: does `G` have a total dominating set of size at most `K`, i.e. a set `D ⊆ V` with `|D| ≤ K` such that every vertex of `V` (including those in `D`) is adjacent to a vertex of `D`?

## Sources

- R. Laskar, J. Pfaff, S. M. Hedetniemi and S. T. Hedetniemi, "On the algorithmic complexity of total domination", SIAM Journal on Algebraic and Discrete Methods 5(3) (1984), 420-425, doi:10.1137/0605040.
