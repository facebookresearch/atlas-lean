# Ben-Or–Tiwari: a hitting set for sparse polynomials

Over an integral domain of characteristic zero, let $p_1,\dots,p_n$ be the first $n$ primes. The $s$ points $(p_1^{j},\dots,p_n^{j})$, $0\le j<s$, form a hitting set for all nonzero $n$-variate polynomials with at most $s$ monomials, of arbitrary degree. More generally the conclusion holds for the powers of any point at which distinct monomials take distinct values.

## Proof sketch

Evaluating $f=\sum_{i=1}^{s}c_im_i$ at the $j$-th powers gives $\sum_ic_i\,m_i(a)^j$; if all vanish for $j<s$, the Vandermonde system in the distinct values $m_i(a)$ forces all $c_i=0$. Distinct monomials take distinct values at $(p_1,\dots,p_n)$ by unique factorization.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)

## Sources

- Michael Ben-Or, Prasoon Tiwari, "A Deterministic Algorithm for Sparse Multivariate Polynomial Interpolation", Proceedings of the 20th Annual ACM Symposium on Theory of Computing (STOC 1988), 1988.
