# 2-SAT witnesses in polynomial time via the implication graph

For a 2-CNF $\varphi$ build the implication graph with an arc $\neg\ell\to\ell'$ and $\neg\ell'\to\ell$ for each clause $\ell\vee\ell'$. $\varphi$ is satisfiable iff no variable $x$ has $x$ and $\neg x$ in a common strongly connected component, and a satisfying assignment is computable in polynomial time by setting each variable according to the topological order of the components of $x$ and $\neg x$ (Aspvall–Plass–Tarjan).

## Proof sketch

Paths in the implication graph are forced implications, so $x\leadsto\neg x\leadsto x$ makes $\varphi$ unsatisfiable. Otherwise assign $x$ true iff the component of $\neg x$ precedes that of $x$ in topological order; no clause can then be violated since that would create an arc against the order.

## Depends on

- [2-SAT as a decision problem](../2-satisfiability/two-sat-dec.md)

## Proof depends on

- [2-SAT is in P](../2-satisfiability/two-sat-in-p.md)

## Sources

- Bengt Aspvall, Michael F. Plass and Robert Endre Tarjan, "A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas", Information Processing Letters 8(3), 1979.
