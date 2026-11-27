# The determinant is not computable by polynomial-size arithmetic AC0 formulas

Over every field of characteristic $0$, the $n \times n$ determinant and the iterated matrix multiplication polynomial $\mathrm{IMM}_{n,d}$ with $d = \lfloor(\log n)/100\rfloor$ require constant-depth arithmetic formulas of superpolynomial size. More precisely, for $d \le (\log n)/100$ (Limaye–Srinivasan–Tavenas, Corollary 4), product-depth-$\Delta$ formulas for $\mathrm{IMM}_{n,d}$ need size $n^{d^{\exp(-O(\Delta))}}$, which is superpolynomial for constant $\Delta$ only when $d$ grows with $n$ (for $d=1$, $\mathrm{IMM}_{n,1}$ is an entry of a single matrix, a variable). Division and $\mathrm{select}$ gates do not help here: for a polynomial of polynomial degree over an infinite field they can be removed with no loss in size or depth beyond polynomial and constant factors (Andrews–Wigderson, Lemma 2.5 and Theorem 2.13). Hence the determinant is not in arithmetic $\mathrm{AC}^0_{\mathbb{F}}$ even in the model with division and piecewise computation, although the resultant and discriminant are in $\mathrm{AC}^0_{\mathbb{F}}$ and the GCD is computable piecewise in $\mathrm{AC}^0_{\mathbb{F}}$ there.

## Proof sketch

This is the Limaye-Srinivasan-Tavenas lower bound for constant-depth circuits computing $\mathrm{IMM}_{n,d}$, applied with a growing $d$ in its range such as $d = \lfloor(\log n)/100\rfloor$, transferred to the determinant through the fact that $\mathrm{IMM}_{n,d}$ is a projection of a determinant of size $\operatorname{poly}(n, d)$ and constant-depth formulas are closed under projections. A constant-depth, polynomial-size circuit for the determinant with division or $\mathrm{select}$ gates would, after removing them, give a division-free one, contradicting the lower bound.

## Depends on

- [Arithmetic AC0: constant-depth arithmetic circuits with division and piecewise computation](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Andrews–Wigderson: resultants, discriminants and Bézout coefficients in arithmetic AC0](aw-resultant-discriminant.md)

## Sources

- N. Limaye, S. Srinivasan, S. Tavenas, "Superpolynomial lower bounds against low-depth algebraic circuits", FOCS (2021), doi:10.1109/FOCS52979.2021.00083; Communications of the ACM 65 (2022), ECCC TR21-081.
- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839 (Section 2.2, Lemma 2.5, Theorem 2.13; Theorems 1.1 and 1.2).
