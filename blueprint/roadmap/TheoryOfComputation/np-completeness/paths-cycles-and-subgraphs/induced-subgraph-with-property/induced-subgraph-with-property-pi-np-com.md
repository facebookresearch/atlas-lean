# INDUCED SUBGRAPH WITH PROPERTY Π is NP-complete

Let $\Pi$ be a graph property that is [hereditary](is-hereditary.md) and
[nontrivial](is-nontrivial.md), and whose [recognition problem](property-dec.md) is in P. Then
the decision problem [INDUCED SUBGRAPH WITH PROPERTY
Π](induced-subgraph-with-property-pi-dec.md) for $\Pi$ belongs to NP, and every decision problem
in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT21] INDUCED SUBGRAPH WITH PROPERTY Π.
- J. M. Lewis and M. Yannakakis, "The node-deletion problem for hereditary properties is NP-complete", Journal of Computer and System Sciences 20 (1980), 219-230, doi:10.1016/0022-0000(80)90060-4.
- V. Raman and S. Sikdar, "Parameterized complexity of the induced subgraph problem in directed graphs", Information Processing Letters 104 (2007), 79-85, doi:10.1016/j.ipl.2007.05.005 (Section 2 restates the Lewis-Yannakakis theorem: NP-hard for every nontrivial hereditary property, NP-complete when the property can moreover be tested in polynomial time).
