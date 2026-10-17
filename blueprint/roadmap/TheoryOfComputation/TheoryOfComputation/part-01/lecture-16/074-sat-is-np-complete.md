---
article_id: af_995a5b255899ca683df5ef33
declaration: theorem
origin: cited
lean: CookLevin.cook_levin
---

# Theorem (SAT is NP-complete)

$\mathrm{SAT}$ is $\mathsf{NP}$-complete. Proof: (1) $\mathrm{SAT} \in \mathsf{NP}$. (2) For each $A \in \mathsf{NP}$, $A \leq_P \mathrm{SAT}$: Let $A \in \mathsf{NP}$ be decided by NTM $M$ in time $n^k$. Give a polynomial-time reduction $f$ mapping $A$ to $\mathrm{SAT}$: $f(w) = \langle \phi_{M,w} \rangle$ where $w \in A$ iff $\phi_{M,w}$ is satisfiable. The formula $\phi_{M,w} = \phi_{\mathrm{cell}} \wedge \phi_{\mathrm{start}} \wedge \phi_{\mathrm{move}} \wedge \phi_{\mathrm{accept}}$ simulates $M$ on $w$. The size of $\phi_{M,w}$ is $O(n^{2k})$, so $f$ is computable in polynomial time.

## Depends on

- [Definition (NP-complete)](../lecture-15/061-np-complete.md)
- [Definition (SAT)](../lecture-14/054-sat.md)

## Proof depends on

- [Definition: Turing Machine](../lecture-5/022-definition-turing-machine.md)
- [Definition (Lecture 14, section on Polynomial Time Reducibility)](../lecture-14/053-definition.md)
- [Definition (Tableau)](072-tableau.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 16, Cook-Levin Theorem (idea) and Conclusion sections](../../../../../sources/v1/TheoryOfComputation.md)
