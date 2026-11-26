# The determinant is not computable by polynomial-size arithmetic AC0 formulas

Over every field of characteristic $0$, the $n \times n$ determinant and the iterated matrix multiplication polynomial $\mathrm{IMM}_{n,d}$ with $d = O(\log n)$ require constant-depth arithmetic formulas of superpolynomial size; more precisely, depth-$\Delta$ formulas for $\mathrm{IMM}_{n,d}$ need size $n^{d^{\exp(-O(\Delta))}}$. Hence, although many linear-algebra problems with symmetric structure (GCD, resultant, discriminant) lie in arithmetic $\mathrm{AC}^0$, the determinant does not.

## Proof sketch

This is the Limaye-Srinivasan-Tavenas lower bound for constant-depth circuits computing $\mathrm{IMM}_{n,d}$ with $d = O(\log n)$, transferred to the determinant through the fact that $\mathrm{IMM}_{n,d}$ is a projection of a determinant of size $\operatorname{poly}(n, d)$ and constant-depth formulas are closed under projections.

## Depends on

- [Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Andrews–Wigderson: resultants, discriminants and Bézout coefficients in arithmetic AC0](aw-resultant-discriminant.md)

## Sources

- N. Limaye, S. Srinivasan, S. Tavenas, "Superpolynomial lower bounds against low-depth algebraic circuits", FOCS (2021); Communications of the ACM 65 (2022), ECCC TR21-081.
- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
