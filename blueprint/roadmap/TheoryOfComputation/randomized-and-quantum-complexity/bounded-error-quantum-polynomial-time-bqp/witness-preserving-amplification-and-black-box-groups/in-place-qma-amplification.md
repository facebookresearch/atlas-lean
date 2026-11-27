# Marriott-Watrous in-place amplification of QMA

Let $a, b : \mathbb{N} \to [0,1]$ be polynomial-time computable with $a(n) - b(n) \ge 1/q(n)$ for a polynomial $q$, and let $r$ be any polynomial. Every promise problem with a QMA verifier of completeness $a$, soundness $b$ and witness length $m(n)$ also has a QMA verifier with completeness $1 - 2^{-r(n)}$, soundness $2^{-r(n)}$ and the *same* witness length $m(n)$, running in time $\mathrm{poly}(n)\cdot r(n) q(n)^2$.

## Proof sketch

Run the alternating-projection procedure for $N = O(r q^2)$ rounds and accept if the fraction of agreeing consecutive outcomes exceeds $(a+b)/2$. By the estimator lemma, conditioned on the Jordan block of eigenvalue $p_j$ the count is binomial with parameter $p_j$. For yes-instances the honest witness can be taken as the top eigenvector with $p \ge a$; for no-instances every eigenvalue is at most $b$. A Chernoff bound gives error $2^{-r}$ in both cases without copying the witness.

## Depends on

- [QMA for promise problems](../../local-hamiltonian-problem/qmapromise.md)

## Proof depends on

- [Alternating projections estimate the acceptance probability of a fixed witness](alternating-projection-acceptance-estimator.md)
- [QMA error reduction by parallel repetition](../../qma-error-reduction-by-parallel-repetition.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
