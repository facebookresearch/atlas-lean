# 3SAT with exactly three distinct variables per clause: NP-complete in general, trivial with three occurrences

Let EU3SAT be satisfiability of CNF formulas in which every clause contains exactly three distinct variables. EU3SAT and its not-all-equal variant are $\mathsf{NP}$-complete. In contrast (Tovey), every EU3SAT formula in which each variable occurs at most three times is satisfiable, so that restriction is in $\mathsf{P}$.

## Proof sketch

Hardness: replace each positive exact-one triple $(a,b,c)$ by the five clauses forbidding the five non-exact-one patterns over the same three variables. Tovey: in the bipartite clause–variable incidence graph each clause has degree $3$ and each variable degree $\le3$, so Hall's condition holds and there is a matching saturating the clauses; set each matched variable to satisfy its clause.

## Depends on

- [The 3SAT decision problem](../satisfiability/3-satisfiability/sat3-dec.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [1-IN-3-SAT is NP-complete](../satisfiability/1-in-3-sat/one-in-three-sat-np-complete.md)
- [NOT-ALL-EQUAL 3-SAT is NP-complete](../satisfiability/not-all-equal-3-sat/nae-three-sat-np-complete.md)

## Sources

- Craig A. Tovey, "A Simplified NP-Complete Satisfiability Problem", Discrete Applied Mathematics 8, 1984.
- Michael R. Garey and David S. Johnson, "Computers and Intractability: A Guide to the Theory of NP-Completeness", W. H. Freeman, 1979.
