# Depth-three $\Sigma_3^k$ formulas

Fix $k \ge 1$. A $\Sigma_3^k$ formula for $f : \{0,1\}^n \to \{0,1\}$ is a disjunction $\varphi_1 \vee \dots \vee \varphi_s$ of CNF formulas each of whose clauses has width at most $k$, computing $f$; its size is $s$. Let $\Sigma_3^k(f)$ be the least such $s$ and $\Pi_3^k(f) = \Sigma_3^k(\neg f)$. These are depth-three circuits with an OR at the top and bottom fan-in at most $k$.

## Depends on

- [CNF formula](../../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [Depth-d circuit size of parity](../../../lower-bounds-for-ac0-circuits/depth-d-circuit-size-of-parity.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science, 1999.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
