# Forbes–Saptharishi–Shpilka: shifted ROABPs are rank concentrated on small supports

A matrix of polynomials $F\in K[x]^{r\times r}$ is *support-$\ell$ rank concentrated at $\alpha$* if the coefficient matrices of $F(x+\alpha)$ on monomials involving at most $\ell$ variables span the coefficient matrices of all monomials. Let $N=2^n$, $d,r\ge1$, let $\pi$ be any permutation of $[N]$, and let $F(x)=\prod_{i=1}^{N}M_i(x_{\pi(i)})$ with each $M_i$ an $r\times r$ matrix of univariate polynomials of degree less than $d$. Let $g(t,s)$ be an independent monomial map for total degree below $2d(\lfloor\log_2r^2\rfloor+1)$ (a polynomial map in fresh variables that keeps all monomials of that degree linearly independent), and let $G=\sum_{i=1}^{n}u_i\,g(t_i,s_i)$ with fresh variables $u_i,t_i,s_i$. Then $F$ is support-$(\lfloor\log_2r^2\rfloor+1)$ rank concentrated at $G$ over the field $K(u,t,s)$, and $G$ does not depend on $\pi$. Consequently every nonzero entry of $F$, that is every nonzero polynomial computed by a width-$r$ ROABP of individual degree below $d$ in any variable order, has after the shift $x\mapsto x+G$ a nonzero coefficient on a monomial involving at most $\lfloor\log_2r^2\rfloor+1$ variables.

## Proof sketch

Induct on $n$, splitting the $N$ variables in half along the order $\pi$, so that $F=G_1(y)\,G_2(z)$ with disjoint $y,z$. Rank concentration of the two halves on supports of size $\ell$ gives, by bilinearity of matrix multiplication, concentration of the product on supports of size $2\ell$; a further shift by $u_n\,g(t_n,s_n)$ acts as a rank condenser and brings the support back to $\lfloor\log_2r^2\rfloor+1$, since the coefficient space has dimension at most $r^2$. A nonzero linear functional of $F$ then sees one of the small-support coefficients.

## Depends on

- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)

## Sources

- Michael A. Forbes, Ramprasad Saptharishi, Amir Shpilka, "Hitting Sets for Multilinear Read-Once Algebraic Branching Programs, in any Order", Proceedings of the 46th Annual ACM Symposium on Theory of Computing (STOC 2014), 2014 (arXiv:1309.5668), Definition 3.1, Lemma 3.3, Lemma 6.1, Corollary 6.2, Lemma 6.3 and Theorem 6.5.
