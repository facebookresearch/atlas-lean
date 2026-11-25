# ACHROMATIC NUMBER on complements of bipartite graphs is NP-complete

The decision problem ACHROMATIC NUMBER on complements of bipartite graphs belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

For a bipartite graph $H$, a proper coloring of its complement partitions the vertices into singleton classes and disjoint edges of $H$. Every class of size two has adjacent representatives in the complement with every other class, since it meets both sides of the bipartition. Thus the coloring is complete exactly when no two unmatched vertices are adjacent in $H$, that is, when the paired edges form a maximal matching. A matching of size $s$ on $n$ vertices gives $n-s$ colors.

## Sources

- Michael R. Garey and David S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER.
- M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", *SIAM Journal on Applied Mathematics* 38 (1980), 364-372, doi:10.1137/0138030.
