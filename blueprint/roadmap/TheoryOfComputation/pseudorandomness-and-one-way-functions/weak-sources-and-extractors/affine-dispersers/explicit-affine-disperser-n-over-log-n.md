# An explicit affine disperser for dimension O(N / log N)

For each $N$ let $\ell = \lfloor\log_2 N\rfloor$, $L = \lfloor \ell/3\rfloor$, and let the field degree $n$ be the product of primes in $(L, 4L]$ chosen greedily in increasing order with product at most $\lfloor N/(\ell+1)^2\rfloor$ ($n = 1$ if none). Take $F = \mathbb{F}_{2^n}$ with the monomial basis in roots of the lexicographically least irreducible polynomials of those prime degrees (so arithmetic needs only polynomials of degree at most $4L$, found by exhaustive search over fewer than $2N^{4/3}$ candidates), $r = \lfloor N/n\rfloor$ blocks, $t = \ell + 1$, $\mu = 1$ and $s = \lfloor n/(L+1)\rfloor$. The resulting function $\{0,1\}^N \to \{0,1\}$ is an affine disperser for dimension $d(N) + 1$ with $d(N) = N - rn + r\max(r+1, s) + r(r+1) + nt + \lfloor nr/t\rfloor$, and $(\lfloor\log_2 N\rfloor + 1)\, d(N) \le 6N$ for all large $N$; thus $d(N) = O(N/\log N)$ and $d(N) < N$ eventually.

## Proof sketch

Every prime factor of $n$ exceeds $L$, so proper subfields have at most $2^s$ elements and the Ben-Sasson–Kopparty bound applies. Each term of $d(N)$ is $O(N/\ell)$ except $2r(r+1)$: either the greedy choice stops within a factor $4L$ of its budget, giving $r = O(\ell^3)$, or it takes all primes in $(L, 4L]$, whose product is large by Chebyshev's estimates.

## Depends on

- [Ben-Sasson–Kopparty: the trace of an elementary symmetric polynomial is an affine disperser](ben-sasson-kopparty-trace-disperser.md)

## Sources

- E. Ben-Sasson and S. Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing, 2012.
- R. Lidl and H. Niederreiter, "Finite Fields", Cambridge University Press, 1997.
- P. L. Chebyshev, "Mémoire sur les nombres premiers", Journal de Mathématiques Pures et Appliquées, 1852.
- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
