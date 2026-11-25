# DEFECTIVE CONCENTRATOR is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given an acyclic directed graph on $\{0, \dots, n - 1\}$, given by a list of distinct loopless arcs, and disjoint lists $I$ and $O$ of distinct input and output vertices with $|O| \le |I|$, decide whether the graph fails to be a concentrator, that is, whether some set of $|O|$ inputs cannot be joined to the outputs by that many pairwise vertex-disjoint directed paths.

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(1) (1985), 145-159, doi:10.1016/0196-6774(85)90025-2, problem [8] DEFECTIVE SUPERCONCENTRATOR, comment ("Also NP-complete are the problems of identifying defective ... 'concentrators'").
- M. Blum, R. M. Karp, O. Vornberger, C. H. Papadimitriou and M. Yannakakis, "The complexity of testing whether a graph is a superconcentrator", Information Processing Letters 13(4-5) (1981), 164-167, doi:10.1016/0020-0190(81)90050-8.
