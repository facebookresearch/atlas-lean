# Andrews–Wigderson: resultants, discriminants and Bézout coefficients in arithmetic AC0

Let $\mathbb{F}$ be a field of characteristic $0$ or of characteristic greater than $2n$, and let $f, g \in \mathbb{F}[x]$ have degree at most $n$, given by their coefficients. In the model of arithmetic circuits with gates $+$, $\times$, $\div$:

- the resultant $\operatorname{Res}(f, g)$ and the discriminant $\operatorname{Disc}(f)$ are in $\mathrm{AC}^0_{\mathbb{F}}$, and so are the entries of the adjugate $\operatorname{adj}\operatorname{Syl}(f, g)$;
- when $\gcd(f, g) = 1$, the Bézout coefficients $u, v$ with $uf + vg = 1$, the inverse $\operatorname{Syl}(f, g)^{-1}$ of the Sylvester matrix and the inverse of the Bézout matrix are in $\mathrm{AC}^0_{\mathbb{F}}$;
- for arbitrary nonzero $f, g$, the Bézout coefficients $u, v$ with $uf + vg = \gcd(f, g)$ and the squarefree decomposition of $f$ are computable piecewise in $\mathrm{AC}^0_{\mathbb{F}}$; for the squarefree decomposition of $f$, characteristic $0$ or greater than $\deg f$ suffices (Lemma 7.6).

## Proof sketch

For monic $f$ of degree $n$, $\operatorname{Res}(f,g) = \prod_i g(\alpha_i)$ over the roots $\alpha_i$ of $f$ is the elementary symmetric polynomial $e_n(g(\alpha_1), \dots, g(\alpha_n))$, which Newton's identities compute from the power sums $\sum_i g(\alpha_i)^k$, themselves computed in constant depth from the coefficients; the discriminant is $\pm\operatorname{Res}(f, f')$. The columns of $\operatorname{adj}\operatorname{Syl}(f, g)$ are coefficient vectors of $a_\ell, b_\ell$ with $a_\ell f + b_\ell g = \operatorname{Res}(f,g)\,x^{\deg f + \deg g - \ell}$, which are expressed through symmetric functions of the roots. Then $\operatorname{Syl}(f,g)^{-1} = \operatorname{adj}\operatorname{Syl}(f,g)/\operatorname{Res}(f,g)$ uses one division, and its last column gives the Bézout coefficients of coprime $f, g$. In general one first divides $f$ and $g$ by their GCD, computed piecewise, and the squarefree decomposition comes from filtering roots by multiplicity.

## Depends on

- [Arithmetic AC0: constant-depth arithmetic circuits with division and piecewise computation](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Andrews–Wigderson: the GCD of two polynomials in arithmetic AC0](aw-gcd-ac0.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839 (Theorem 1.2; Theorems 6.1, 6.7 and 6.10, Corollaries 6.2, 6.8 and 8.3, Lemma 7.6).
