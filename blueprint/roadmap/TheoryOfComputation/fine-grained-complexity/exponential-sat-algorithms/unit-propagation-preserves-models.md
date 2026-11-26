# Unit propagation preserves models and terminates

Let $\varphi$ be a CNF formula containing a unit clause $\{\ell\}$. Every model of $\varphi$ sets $\ell$ true, and $\varphi$ is satisfiable iff its restriction $\varphi\restriction_{\ell = 1}$ (delete satisfied clauses and the literal $\neg \ell$ elsewhere) is satisfiable. Iterating unit propagation removes at least one clause per step, so it terminates after at most $|\varphi|$ steps, either with a formula without unit clauses or with the empty clause.

## Proof sketch

Direct from the restriction lemma; termination by the decreasing number of clauses.

## Depends on

- [Restriction of a CNF formula by a literal](../../../Logic/propositional-logic/conjunctive-normal-form/restrict-2.md)

## Proof depends on

- [Unit propagation preserves satisfiability](../../../Logic/propositional-logic/conjunctive-normal-form/sat-iff-restrict-of-unit.md)

## Sources

- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021.
