# Quasipolynomial hitting sets for ROABPs in unknown order

Over a field of characteristic zero, there is an explicit set $H\subseteq F^n$ of size $(n\delta w)^{O(\log n)}$, independent of the variable order, that contains a non-root of every nonzero $n$-variate polynomial computed by a width-$w$ ROABP (in some order) whose layer entries have degree at most $\delta$. The construction substitutes $x_i\mapsto t^{\mathrm{wt}(x_i)}$ for each of a quasipolynomial family of candidate weight functions, one of which is a basis-isolating weight assignment for the ROABP, and evaluates the resulting univariate polynomials at enough points.

## Proof sketch

Write the ROABP as $R\cdot D(x)$ with $D(x)=\prod_iD_i(x_{\pi(i)})$ a product of univariate $w\times w$ matrices; the coefficients of $D$ lie in the $w^2$-dimensional matrix algebra. A weight function isolates a basis if a set of at most $w^2$ monomials spans all coefficients with every other coefficient spanned by those of strictly smaller weight; then the univariate substitution keeps a nonzero ROABP nonzero. Such a weight function is built as a combination of $\lceil\log_2n\rceil+1$ weight functions, each a Kronecker map reduced modulo one of polynomially many small primes, merging pairs of adjacent segments of the order at each level, at total cost $(nw\delta)^{O(\log n)}$.

## Depends on

- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)

## Sources

- Manindra Agrawal, Rohit Gurjar, Arpita Korwar, Nitin Saxena, "Hitting-Sets for ROABP and Sum of Set-Multilinear Circuits", SIAM Journal on Computing, 2015 (arXiv:1406.7535), Lemma 4, Lemma 8 and Theorem 1.
