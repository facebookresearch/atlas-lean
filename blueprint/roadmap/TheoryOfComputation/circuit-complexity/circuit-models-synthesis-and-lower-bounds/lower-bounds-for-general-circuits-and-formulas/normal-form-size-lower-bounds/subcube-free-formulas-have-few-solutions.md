# Formulas without large solution subcubes have few solutions

Let $\psi$ be a $k$-CNF formula over $N$ variables in which every variable shares a clause with at most $\Delta$ other variables, and suppose the set of solutions of $\psi$ contains no subcube of dimension $D$. Then every solution has at most $(D-1)(\Delta+1)$ pairwise separated directions along which it can be moved within the solutions, and consequently $|\psi^{-1}(1)| \le 2^{(1 - 1/k + \varepsilon) N + C D}$ for constants depending on $k$, $\varepsilon$ and $\Delta$. Combined with sparsification this gives $|f^{-1}(1)| \le \Sigma_3^k(f) \cdot 2^{(1-1/k+\varepsilon)N + CD}$ for every $f$ whose true inputs contain no $D$-dimensional subcube.

## Proof sketch

Moves supported on clause-disjoint variable sets can be combined independently, so many separated moves would produce a large subcube of solutions; bounding separated moves bounds the non-isolated directions, and the coding lemma applies to the remaining isolated directions.

## Depends on

- [Depth-three $\Sigma_3^k$ formulas](depth-three-sigma3-formulas.md)

## Proof depends on

- [A $k$-CNF has at most $2^{(1-1/k)n}$ isolated solutions](../../../../fine-grained-complexity/exponential-sat-algorithms/k-cnf-isolated-solutions-bound.md)
- [Impagliazzo–Paturi–Zane sparsification lemma](../../../../fine-grained-complexity/sparsification-lemma/impagliazzo-paturi-zane-sparsification-lemma.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science, 1999.
- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
