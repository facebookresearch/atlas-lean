# MINIMUM 3DNF SATISFIABILITY is NP-complete

The decision problem MINIMUM 3DNF SATISFIABILITY belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from NON-TAUTOLOGY for 3DNF expressions, which asks for an assignment satisfying no term. Append the two singleton terms $z$ and $\lnot z$ on a fresh variable $z$ and set $K = 1$: exactly one added term holds under every assignment, so the new instance is accepted exactly when the original expression has an assignment satisfying none of its terms. The bound $K = 0$ is not available, since well-formed instances have $K \ge 1$.

## Sources

- P. Crescenzi and V. Kann, *A compendium of NP optimization problems* (2000), problem MINIMUM 3DNF SATISFIABILITY ("Instance: Set U of variables, collection C of conjunctive clauses of at most three literals ... Measure: Number of clauses satisfied by the truth assignment"), which the compendium relates to Garey and Johnson's [LO8].
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO8] NON-TAUTOLOGY, comment: remains NP-complete for expressions in disjunctive normal form with three literals per disjunct.
- S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the 3rd Annual ACM Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
