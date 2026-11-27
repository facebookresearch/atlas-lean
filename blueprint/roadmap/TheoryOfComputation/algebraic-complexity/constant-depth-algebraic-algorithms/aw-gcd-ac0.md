# Andrews–Wigderson: the GCD of two polynomials in arithmetic AC0

Let $\mathbb{F}$ be a field of characteristic $0$ or of characteristic greater than $2n$. There are piecewise arithmetic circuits (gates $+$, $\times$, $\div$ and $\mathrm{select}$) of unbounded fan-in, constant depth and size $\operatorname{poly}(n)$ that, on input the coefficient vectors of two nonzero polynomials $f, g \in \mathbb{F}[x]$ of degree at most $n$, output the coefficients of the monic $\gcd(f, g)$. That is, the GCD is computable piecewise in $\mathrm{AC}^0_{\mathbb{F}}$; so is $\mathrm{lcm}(f, g)$. Piecewise computation cannot be avoided, since the GCD is not a rational function of the input coefficients.

## Proof sketch

Write $f = \prod_i (x - \alpha_i)^{a_i}$ and $g = \prod_i (x - \alpha_i)^{b_i}$ over the algebraic closure. Power sums of the roots, and through Newton's identities the elementary symmetric functions $e_k(h(\alpha_1), \dots, h(\alpha_n))$ for a polynomial $h$, are computed in constant depth from the coefficients. Selecting the largest $k$ with $e_k \ne 0$ (a $\mathrm{select}$ gate) gives the product of the nonzero values $h(\alpha_i)$, which filters the roots of $f$ according to whether $h$ vanishes on them, and by applying this to derivatives, according to their multiplicities. Exact division and $r$-th roots of perfect powers are computed in constant depth through Newton series. This gives the squarefree part $s$ of $fg$ and, for each $r$, the product $s_{\ge r}$ of the factors $x - \alpha_i$ with $a_i \ge r$ and $b_i \ge r$; then $\gcd(f, g) = \prod_{r} s_{\ge r}$, whose coefficients are obtained by interpolation. Dividing $fg$ by the GCD gives the LCM.

## Depends on

- [Arithmetic AC0: constant-depth arithmetic circuits with division and piecewise computation](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Constant-depth formulas for power sums of roots](power-sums-from-coefficients.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839 (Theorem 1.1, Theorem 8.1, Corollary 8.2; Lemmas 5.3, 7.3, 7.4 and Corollary 7.7).
