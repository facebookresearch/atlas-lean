# Shifted partials of design polynomials are near-maximal

Let $P = \mathrm{NW}_{q,d,k}$ be the Nisan-Wigderson design polynomial in $N = qd$ variables. For $k' \le \min(k, d - k)$, the $k'$-th order partial derivatives of $P$ along design directions have pairwise distinct leading monomials, and for some shift degree $\ell \le N^{O(1)}$, $\mathrm{SP}_{k',\ell}(P)$ is at least a $2^{-O(d)}$ fraction of the minimum of the trivial upper bound and $q^{k'}$ times the number of degree-$\ell$ monomials in $N$ variables. Hence design polynomials achieve shifted-partials dimension within a $2^{-O(d)}$ factor of the largest value permitted by their number of derivatives.

## Proof sketch

Distinct degree-$<k$ polynomials $h$ give monomials that pairwise share fewer than $k$ variables, so after differentiating along $k' \le \min(k, d-k)$ design variables (so that each leading monomial, of degree $d - k' \ge k$, determines $h$) the resulting derivatives have distinct leading monomials that remain distinct after multiplication by shifts unless the shifts collide, which happens rarely by an inclusion-exclusion count. Counting distinct leading monomials of shifted derivatives lower-bounds the span dimension.

## Depends on

- [Projected shifted partials and the Nisan–Wigderson design polynomial](projected-shifted-partials.md)
- [The dimension of shifted partial derivatives](shifted-partials-measure.md)

## Sources

- N. Kayal, C. Saha, R. Saptharishi, "A super-polynomial lower bound for regular arithmetic formulas", STOC (2014), ECCC TR13-091.
- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Approaching the chasm at depth four", Journal of the ACM 61 (2014); CCC (2013).
