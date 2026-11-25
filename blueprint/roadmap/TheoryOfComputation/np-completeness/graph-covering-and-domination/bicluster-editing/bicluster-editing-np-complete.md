# BICLUSTER EDITING is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a bipartite graph with sides $\{0, \dots, p - 1\}$ and $\{0, \dots, q - 1\}$, given by an edge list without repeated pairs, and a natural number $K$, decide whether adding and deleting at most $K$ pairs $(u, v)$ with $u$ and $v$ on different sides turns it into a graph whose connected components are all bicliques (single vertices allowed).

## Sources

- N. Amit, "The bicluster graph editing problem", M.Sc. thesis, Tel Aviv University (2004), supervised by R. Shamir (Section 1.4: the definitions of bicluster graphs, bicluster editing sets and BICLUSTER GRAPH EDITING; Chapter 2, Theorem: "Bicluster Graph Editing is NP-complete", by a reduction from exact cover by 3-sets).
