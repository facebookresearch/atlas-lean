# Weighted independent set on $K_{1,4}$- and diamond-free graphs is NP-complete

Statement: the decision problem WEIGHTED INDEPENDENT SET on $(K_{1,4}, \text{diamond})$-free graphs, with natural-number weights and target in binary, belongs to NP, and every decision problem $L$ in NP is polynomial-time many-one reducible to it: there is a function $f$ from bitstrings to bitstrings, computable in polynomial time, such that $x \in L$ exactly when $f(x)$ is accepted, for every bitstring $x$.

An instance consists of a graph $G$ with no induced star $K_{1,4}$ and no induced diamond ($K_4$ minus an edge), a weight $w(v) \in \mathbb{Z}_{\ge 0}$ for each vertex, and a number $k \in \mathbb{Z}_{\ge 0}$; the question is whether $G$ has a set $S$ of pairwise non-adjacent vertices with $\sum_{v \in S} w(v) \ge k$.

## Sources

- D. G. Corneil, "The complexity of generalized clique packing", *Discrete Applied Mathematics* 12 (1985), 233–239, <https://doi.org/10.1016/0166-218X(85)90027-7>.
- A. Brandstädt, V. B. Le and S. Mahfud, "New applications of clique separator decomposition for the Maximum Weight Stable Set problem", *Theoretical Computer Science* 370 (2007), 229–239, <https://doi.org/10.1016/j.tcs.2006.10.035>.
- ISGCI, Information System on Graph Classes and their Inclusions, problem "Weighted independent set" on the class $(K_{1,4}, \text{diamond})$-free (gc_413).
