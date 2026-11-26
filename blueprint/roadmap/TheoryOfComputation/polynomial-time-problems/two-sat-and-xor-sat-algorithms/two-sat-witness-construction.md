# 2-SAT witnesses in polynomial time via the implication graph

There is a polynomial-time (indeed linear-time) algorithm that, given a 2-CNF $\varphi$ (every clause has at most two literals), outputs a satisfying assignment of $\varphi$ if one exists and reports that $\varphi$ is unsatisfiable otherwise. If $\varphi$ contains the empty clause it is unsatisfiable. Otherwise the algorithm builds the implication graph, with arcs $\neg\ell\to\ell'$ and $\neg\ell'\to\ell$ for each clause $\ell\vee\ell'$ and the arc $\neg\ell\to\ell$ for each unit clause $\ell$, computes its strongly connected components in a topological order, and, when no variable $x$ has $x$ and $\neg x$ in a common component, sets $x$ true exactly when the component of $\neg x$ precedes that of $x$ (Aspvall–Plass–Tarjan).

## Proof sketch

The empty-clause test, the graph and its strongly connected components (Tarjan's algorithm) take linear time. If some $x$ shares a component with $\neg x$, the formula is unsatisfiable by the characterization. Otherwise the assignment is well defined, and it is consistent along arcs: a clause it violated would give an arc from a true literal to a false one, which runs against the topological order of the components.

## Depends on

- [2-SAT as a decision problem](../2-satisfiability/two-sat-dec.md)

## Proof depends on

- [2-SAT characterization](../../../Logic/propositional-logic/2-satisfiability/cnf-sat-iff-of-is-two-cnf.md)

## Sources

- Bengt Aspvall, Michael F. Plass and Robert Endre Tarjan, "A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas", Information Processing Letters 8(3), 1979.
