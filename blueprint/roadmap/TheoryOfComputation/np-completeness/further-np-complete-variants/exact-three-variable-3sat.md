# 3SAT with exactly three distinct variables per clause: NP-complete in general

Let EU3SAT be satisfiability of CNF formulas in which every clause contains exactly three distinct variables. EU3SAT and its not-all-equal variant are $\mathsf{NP}$-complete.

## Proof sketch

Membership in $\mathsf{NP}$ is clear. Hardness of EU3SAT: reduce from positive 1-in-3-SAT with three distinct variables per clause, replacing each triple $(a,b,c)$ by the five clauses forbidding the five non-exact-one patterns $000,110,101,011,111$ over the same three variables. Hardness of the not-all-equal variant: in a NAE-3SAT instance, drop clauses containing a complementary pair (always NAE-satisfied), replace a clause $\mathrm{NAE}(\ell,\ell,\ell')$ by $\ell\ne\ell'$, and express $\ell\ne\ell'$ with a fresh variable $z$ as $\mathrm{NAE}(\ell,\ell',z)\wedge\mathrm{NAE}(\ell,\ell',\neg z)$; clauses of the form $\mathrm{NAE}(\ell,\ell,\ell)$ are unsatisfiable and are mapped to a fixed unsatisfiable instance.

## Depends on

- [The 3SAT decision problem](../satisfiability/3-satisfiability/sat3-dec.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Not-all-equal satisfiability](../satisfiability/exact-one-and-not-all-equal-satisfiability/not-all-equal-satisfiability.md)

## Proof depends on

- [1-IN-3-SAT is NP-complete](../satisfiability/1-in-3-sat/one-in-three-sat-np-complete.md)
- [NOT-ALL-EQUAL 3-SAT is NP-complete](../satisfiability/not-all-equal-3-sat/nae-three-sat-np-complete.md)

## Sources

- Craig A. Tovey, "A Simplified NP-Complete Satisfiability Problem", Discrete Applied Mathematics 8(1), 85–89, 1984.
- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- Michael R. Garey and David S. Johnson, "Computers and Intractability: A Guide to the Theory of NP-Completeness", W. H. Freeman, 1979.
