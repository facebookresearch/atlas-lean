# Fourier measurement of a family of $\pm1$ observables

Let $A(a)$, $a\in\{0,1\}^n$, be $\pm1$ observables (self-adjoint, $A(a)^2 = 1$) in a star-ordered algebra. Their *Fourier coefficients* are $\hat A(u) = \mathbb{E}_a(-1)^{u\cdot a}A(a)$ for $u\in\{0,1\}^n$; they are self-adjoint and, by Parseval, $\sum_u\hat A(u)^2 = \mathbb{E}_aA(a)^2 = 1$. The *Fourier measurement* is the measurement with outcomes $u\in\{0,1\}^n$ and effects $B_u = \hat A(u)^2$. Moreover $\sum_u\hat A(u)^3 = \mathbb{E}_{a,b}A(a)A(b)A(a+b)$.

## Proof sketch

Self-adjointness and Parseval follow by expanding $\hat A(u)^2$ and averaging the characters $(-1)^{u\cdot(a+a')}$ over $u$; the cubic identity follows in the same way from $\mathbb{E}_u(-1)^{u\cdot(a+b+c)} = \mathbf{1}_{c = a+b}$.

The following fact is derived here and is not stated in the cited source: if $A$ is exactly linear ($A(a)A(b) = A(a+b)$), then each $\hat A(u)$ is a projection, so $B$ is projective with $B_u = \hat A(u)$, and its character observables are $\chi_B(a) = \sum_u(-1)^{a\cdot u}\hat A(u) = A(a)$ by Fourier inversion.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](../states-and-measurements-on-operator-algebras/algebraic-measurements-and-agreement.md)
- [Walsh character on the Boolean cube](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-walsh-char.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017; full version arXiv:1610.03574v1, Section 3, proof of Theorem 10.
