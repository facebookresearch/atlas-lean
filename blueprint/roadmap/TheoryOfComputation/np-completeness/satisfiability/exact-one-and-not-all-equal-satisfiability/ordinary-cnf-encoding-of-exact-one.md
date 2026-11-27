# Ordinary CNF encoding of exact-one semantics

For every clause formula $\varphi$ there is a CNF formula $\mathrm{EO}(\varphi)$ on the same variables, with no auxiliary variables, such that an assignment satisfies $\mathrm{EO}(\varphi)$ (in the ordinary sense) if and only if it one-satisfies $\varphi$: each clause $\ell_1 \vee \dots \vee \ell_k$ contributes itself and the clauses $\neg \ell_i \vee \neg \ell_j$ for all pairs of positions $i < j$. For a clause of three literals on distinct variables, five clauses on those variables suffice. The encoding is computable in polynomial time and preserves model counts.

## Proof sketch

The at-least-one clause forbids zero true occurrences, and the pairwise clauses forbid two; for three literals the truth table has exactly five forbidden patterns of weight $0$ or $\ge 2$.

## Depends on

- [Exact-one satisfiability of a clause formula](exact-one-satisfiability.md)
- [Exactly-one (one-hot) constraint in CNF](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/exactly-one-cnf-constraint.md)

## Sources

- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- T. Walsh, "SAT v CSP", Principles and Practice of Constraint Programming — CP 2000, LNCS 1894, 441–456, 2000.
