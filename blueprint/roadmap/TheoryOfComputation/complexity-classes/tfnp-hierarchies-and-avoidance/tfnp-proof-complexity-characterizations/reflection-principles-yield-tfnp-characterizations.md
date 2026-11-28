# A closed proof system with short proofs of its own reflection principle is characterized by a black-box TFNP problem

A proof system closed under decision-tree reductions that has polylogarithmic-complexity proofs of an efficiently verifiable reflection principle about itself is characterized by the search problem of that principle; conversely every black-box TFNP problem characterizes such a proof system.

**Setting.** $\mathrm{TFNP}^{dt}$ and decision-tree reductions (formulations) are as on [query total search problems](query-tfnp-and-formulations.md), the false-clause search problem $S_F$ and the complexity $P(F) = \min(\deg + \log \mathrm{size})$ as on [the false-clause search problem](false-clause-search-problem.md), and characterization in the polylogarithmic sense of [Characterizing a proof system by a black-box TFNP problem](tfnp-characterization-of-proof-systems.md). A proof system $P$ is **closed under decision-tree reductions** if whenever $F$ has a $P$-proof of complexity $c$ and $H$ reduces to $F$ by depth-$d$ decision trees, $H$ has a $P$-proof of complexity $O(cd)$. A **verification procedure** $V$ for $P$ maps $(n, m, c)$ to a CNF $V_{n,m,c}(H, \Pi)$ whose variables encode an $n$-variable CNF $H$ with $m$ clauses of width at most $c$ and a purported complexity-$c$ (or $O(c)$) $P$-proof $\Pi$ of $H$, such that any error in $\Pi$ is witnessed by at most polylogarithmically many variables, and which has $2^{\Theta(c)}$ variables. The **reflection principle** $\mathrm{Ref}_{P,V}$ is the unsatisfiable CNF

$$
\mathrm{Proof}_{n_H, m_H, c}(H, \Pi) \wedge \mathrm{Sat}_{n_H, m_H, c}(H, \alpha),
$$

where $\mathrm{Proof} := V_{n_H, m_H, c}$ and $\mathrm{Sat}$ states that the assignment $\alpha$ satisfies $H$; its search problem $S_{\mathrm{Ref}}$ lies in $\mathrm{TFNP}^{dt}$.

**Theorem.**

1. For any $\mathrm{TFNP}^{dt}$ problem $R$ there is a proof system $P$ such that $R$ characterizes $P$. Furthermore, $P$ is closed under decision-tree reductions and there is a reflection principle $\mathrm{Ref}_P$ for $P$ with $P(\mathrm{Ref}_P) \le \mathrm{polylog}(n)$.
2. For any proof system $P$ that is closed under decision-tree reductions and for which there is a reflection principle $\mathrm{Ref}_P$ of which $P$ has $\mathrm{polylog}(n)$-complexity proofs, there is a $\mathrm{TFNP}^{dt}$ problem $R$ that characterizes $P$.

Quantitatively, for $P$ closed under decision-tree reductions, any verification procedure $V$, $\mathrm{Ref} = \mathrm{Ref}_{P,V}$ and every unsatisfiable CNF $H$,

$$
S^{dt}_{\mathrm{Ref}}(S_H) \in O(P(H)), \qquad P(H) \in O\big(S^{dt}_{\mathrm{Ref}}(S_H) \cdot P(\mathrm{Ref})\big),
$$

so $S_{\mathrm{Ref}}$ characterizes $P$ when $P(\mathrm{Ref}) = \mathrm{polylog}(n)$. Here $n$ is the number of variables of the formula in question.

## Expansion

For part 2, a $P$-proof $\Pi$ of $H$ gives a reduction from $S_H$ to $S_{\mathrm{Ref}}$ by hard-wiring $H$ and $\Pi$ with constant decision trees and leaving only $\alpha$ free: since $\Pi$ is valid, every solution is a clause of $H$ falsified by $\alpha$. Conversely, closure under reductions turns a short proof of $\mathrm{Ref}$ and a shallow reduction from $S_H$ into a short proof of $H$. For part 1, the canonical proof system $P_F$ of $S_F \in \mathrm{TFNP}^{dt}$ takes as proofs of $H$ the decision trees of a reduction from $S_H$ to an instance of $S_F$, checked by verifying that each clause of the substituted formula is tautological or weakens a clause of $H$; then $S_F^{dt}(S_H) = \Theta(P_F(H))$ (Theorem 4), and encoding reductions by generic decision trees gives a reflection principle $\mathrm{Ref}_F$ with $P_F(\mathrm{Ref}_F) \le \mathrm{polylog}(n)$ (Theorem 5). As an instance the paper introduces IND-PPA, whose complete problem is a leaf-finding problem over a dag of pools, and proves that $\mathbb{F}_2$-Polynomial Calculus is characterized by it, $\text{IND-LEAF}^{dt}(S_F) = \Theta(\mathbb{F}_2\text{-PC}(F))$ (Theorem 7), and that it has polylogarithmic-complexity proofs of its own reflection principle (Theorem 10).

## Depends on

- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)
- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Characterizing a proof system by a black-box TFNP problem](tfnp-characterization-of-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Noah Fleming, Russell Impagliazzo, "TFNP Characterizations of Proof Systems and Monotone Circuits", *14th Innovations in Theoretical Computer Science Conference (ITCS 2023)*, LIPIcs, 2023, doi:10.4230/LIPIcs.ITCS.2023.30 (Theorem 1 in its formal statement in Section 2, Theorems 4, 5 and 6; Theorems 7 and 10 for the Polynomial Calculus example).
