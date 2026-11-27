# Universal property of the free profinite monoid

Every morphism $\varphi$ from $A^*$ to a finite monoid $M$ (with the discrete metric) is uniformly continuous and extends uniquely to a uniformly
continuous morphism $\hat\varphi : \widehat{A^*} \to M$ on the [free profinite monoid](free-profinite-monoid.md). Equivalently, every map from $A$ to a finite monoid $M$ extends uniquely to a
continuous monoid morphism $\hat\varphi : \widehat{A^*} \to M$, which is surjective exactly when the image of $A$ generates $M$. For each profinite word $x$ the sequence
$(x^{n!})_{n > 0}$ converges to an idempotent profinite word $x^\omega$, and $\hat\varphi(x^\omega) = \hat\varphi(x)^\omega$, the unique idempotent power of $\hat\varphi(x)$ in $M$.

## Depends on

- [The profinite metric and the free profinite monoid](free-profinite-monoid.md)

## Sources

- J.-É. Pin, *Mathematical Foundations of Automata Theory*, lecture notes, version of March 24, 2025, <https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf>: Section X.2.2, Proposition X.2.10; Section X.2.3, Proposition X.2.11; and Proposition X.2.14 with the computation of the image of $x^\omega$ that follows it.
