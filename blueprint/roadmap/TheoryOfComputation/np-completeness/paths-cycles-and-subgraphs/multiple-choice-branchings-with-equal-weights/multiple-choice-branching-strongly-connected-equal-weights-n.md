# MULTIPLE CHOICE BRANCHING ON STRONGLY CONNECTED DIGRAPHS WITH EQUAL WEIGHTS is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a strongly connected directed graph on $\{0, \dots, n - 1\}$ whose arcs all have the same positive weight, a partition of its arcs into classes and a positive integer $K$, decide whether some set of arcs of total weight at least $K$ is a branching (no directed cycle and no two arcs entering the same vertex) containing at most one arc from each class.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND11] MULTIPLE CHOICE BRANCHING, p. 208, comment: "Remains NP-complete even if G is strongly connected and all weights are equal" (the entry's reference is [Garey and Johnson, ——], unpublished; transformation from 3SAT).
