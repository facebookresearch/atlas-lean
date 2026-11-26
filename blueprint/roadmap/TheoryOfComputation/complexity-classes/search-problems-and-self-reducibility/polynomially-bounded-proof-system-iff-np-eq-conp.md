# Cook–Reckhow: a polynomially bounded proof system exists iff NP = coNP

There is a polynomially bounded proof system for the set of unsatisfiable CNF formulas (equivalently, for TAUTOLOGY) if and only if $\mathsf{NP}=\mathsf{coNP}$.

## Proof sketch

A polynomially bounded system gives NP certificates for UNSAT, which is coNP-complete, so $\mathsf{coNP}\subseteq\mathsf{NP}$. Conversely, if UNSAT has an NP verifier $V$, the function mapping $\langle\varphi,w\rangle$ to $\varphi$ when $V(\varphi,w)=1$ and to a fixed unsatisfiable formula otherwise is a polynomially bounded proof system.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [The complexity class NP](../the-classes-p-np-and-conp/np.md)
- [The class coNP](../the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [UNSAT is coNP-complete](../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Appendices", 2007, Theorem B.13.
