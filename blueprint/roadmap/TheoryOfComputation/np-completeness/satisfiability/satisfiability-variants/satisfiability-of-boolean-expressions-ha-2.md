# SATISFIABILITY OF BOOLEAN EXPRESSIONS OVER B is NP-complete

For every list $B$ of connective codes that expresses $x \wedge \neg y$, the decision problem SATISFIABILITY OF BOOLEAN EXPRESSIONS OVER B belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO7] SATISFIABILITY OF BOOLEAN EXPRESSIONS, comment (pp. 260-261): "Remains NP-complete if `B` is restricted to `{∧, ∨, →, ¬}`, or any other truth-functionally complete set of connectives. Also NP-complete for any truth-functionally incomplete set of connectives containing `{↛}`, `{↚}`, `{≢, ∨}`, or `{≢, ∧}` as a subset [Lewis, 1978]. Problem is solvable in polynomial time for any truth-functionally incomplete set of connectives *not* containing one of these four sets as a subset.".
- H. R. Lewis, "Satisfiability problems for propositional calculi", Mathematical Systems Theory 13 (1979), 45-53, doi:10.1007/BF01744287.
