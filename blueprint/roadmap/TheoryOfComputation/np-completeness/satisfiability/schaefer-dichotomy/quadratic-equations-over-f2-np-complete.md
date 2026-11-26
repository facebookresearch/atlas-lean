# Quadratic equations over $\mathbb{F}_2$ are NP-complete

The problem QUADEQ, given a system of quadratic equations $\sum_{i \le j} a_{ij} u_i u_j = b$ over $\mathbb{F}_2$ in $0/1$ variables (diagonal monomials $u_i u_i = u_i$ serving as linear terms), decide whether it has a solution, is NP-complete. A 3-CNF clause $\ell_1 \vee \ell_2 \vee \ell_3$ is expressed by one equation $(1 \oplus \ell_1)(1 \oplus \ell_2) = w$ with an auxiliary variable $w$ and the equation $w (1 \oplus \ell_3) = 0$, where a negated variable $\bar x$ is read as $1 \oplus x$.

## Proof sketch

Membership in NP is clear. The clause gadget has a solution exactly when the clause holds, with $w$ determined by $\ell_1,\ell_2$; conjoin the gadgets for all clauses of a 3-CNF.

## Depends on

- [Boolean constraint languages and CSP(Γ)](../polymorphisms-of-boolean-relations/boolean-constraint-languages.md)

## Proof depends on

- [3SAT is NP-complete](../3-satisfiability/sat3-dec-np-complete.md)

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009.
