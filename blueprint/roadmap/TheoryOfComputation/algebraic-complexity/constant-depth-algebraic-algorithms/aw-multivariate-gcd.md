# Andrews–Wigderson: multivariate GCD of polynomials given by constant-depth circuits

Let $\mathbb{F}$ be a field of characteristic $0$ or of characteristic greater than $4d$, and let $f, g \in \mathbb{F}[x_1, \dots, x_n]$ of degree at most $d$ be computed by arithmetic $\mathrm{AC}^0_{\mathbb{F}}$ circuits, that is, constant-depth circuits of size $s$ with $s$ and $d$ polynomial in the input size. Then $\gcd(f, g)$ and the elements of the squarefree decomposition of $f$ (for the latter, characteristic $0$ or greater than $d$ suffices) are computed by $\mathrm{AC}^0_{\mathbb{F}}$ circuits of polynomial size, and these output circuits are ordinary circuits, without $\mathrm{select}$ gates; over an infinite field, division elimination makes them division-free. The output circuits are constructed by a deterministic polynomial-time algorithm with an oracle for polynomial identity testing of such circuits. The oracle can be replaced by randomized identity testing, and, over characteristic $0$ and for depth $o(\log\log\log n)$, by the deterministic subexponential-time identity test that follows from the Limaye–Srinivasan–Tavenas lower bounds.

## Proof sketch

Using the identity-testing oracle, find a point $\alpha$ where the top-degree homogeneous components of $f$ and $g$ do not vanish, and set $\hat f(x, y) = f(x + y\alpha)/f_{\mathrm{top}}(\alpha)$ (and similarly $\hat g$), which is monic in the fresh variable $y$ and has irreducible factors in bijection with those of $f$. By Gauss's lemma, the GCD and squarefree decomposition of $\hat f, \hat g$ over $\mathbb{F}(x)[y]$ give those over $\mathbb{F}[x, y]$. Interpolation gives constant-depth circuits for the $y$-coefficients, the univariate piecewise $\mathrm{AC}^0_{\mathbb{F}}$ algorithms are run on these coefficients, and each $\mathrm{select}$ gate, taken in topological order, is replaced by its first input that is not identically zero, found with the oracle. Undoing the change of variables gives the result.

## Depends on

- [Arithmetic AC0: constant-depth arithmetic circuits with division and piecewise computation](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Andrews–Wigderson: the GCD of two polynomials in arithmetic AC0](aw-gcd-ac0.md)
- [Andrews–Wigderson: resultants, discriminants and Bézout coefficients in arithmetic AC0](aw-resultant-discriminant.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839 (Theorem 1.6; Theorems 10.6, 10.7 and 10.8).
- N. Limaye, S. Srinivasan, S. Tavenas, "Superpolynomial lower bounds against low-depth algebraic circuits", FOCS (2021); Communications of the ACM 65 (2022), ECCC TR21-081.
