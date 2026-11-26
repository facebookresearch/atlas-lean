# 3SAT with exactly three distinct variables per clause: NP-complete in general

Let EU3SAT be satisfiability of CNF formulas in which every clause contains exactly three distinct variables. EU3SAT and its not-all-equal variant are $\mathsf{NP}$-complete.

## Proof sketch

Hardness: replace each positive exact-one triple $(a,b,c)$ by the five clauses forbidding the five non-exact-one patterns over the same three variables.

## Depends on

- [The 3SAT decision problem](../satisfiability/3-satisfiability/sat3-dec.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [1-IN-3-SAT is NP-complete](../satisfiability/1-in-3-sat/one-in-three-sat-np-complete.md)
- [NOT-ALL-EQUAL 3-SAT is NP-complete](../satisfiability/not-all-equal-3-sat/nae-three-sat-np-complete.md)

## Sources

- Craig A. Tovey, "A Simplified NP-Complete Satisfiability Problem", Discrete Applied Mathematics 8, 1984.
- Michael R. Garey and David S. Johnson, "Computers and Intractability: A Guide to the Theory of NP-Completeness", W. H. Freeman, 1979.
