# CONJUNCTIVE QUERY FOLDABILITY is NP-complete

The decision problem CONJUNCTIVE QUERY FOLDABILITY, which asks for a substitution $\sigma$ of the undistinguished variables of $Q_1$ that turns $Q_1$ into $Q_2$ (atoms compared as sets), belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR30] CONJUNCTIVE QUERY FOLDABILITY, p. 233 (reference [Chandra and Merlin, 1977]; transformation from GRAPH 3-COLORABILITY). The problem stated here is this catalogue problem of arbitrary substitution, whose hardness is the catalogue's transformation from GRAPH 3-COLORABILITY; it is not the fold of Chandra and Merlin, which fixes its image and preserves equivalence. Substituting $y_0$ for $y_1$ sends $R(y_0) \wedge S(y_1)$ onto $R(y_0) \wedge S(y_0)$, a substitution in the sense here, although on nonempty disjoint $R$ and $S$ the first Boolean query is true and the second false.
- A. K. Chandra and P. M. Merlin, "Optimal implementation of conjunctive queries in relational data bases", Proceedings of the 9th Annual ACM Symposium on Theory of Computing (STOC 1977), 77-90, doi:10.1145/800105.803397 (folding, defined before Theorem 10).
