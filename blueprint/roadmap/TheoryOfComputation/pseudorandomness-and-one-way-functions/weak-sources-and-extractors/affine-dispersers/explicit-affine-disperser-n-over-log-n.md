# An explicit affine disperser for dimension O(N / log N)

For each $N$ let $n$ be the smallest prime greater than $2N^{3/5}$, $r=\lceil N/n\rceil$ and $t=\lceil\sqrt r\rceil$; fix an injective $\mathbb{F}_2$-linear map $\varphi=(\varphi_1,\dots,\varphi_r):\{0,1\}^N\to\mathbb{F}_{2^n}^r$ and a nontrivial $\mathbb{F}_2$-linear map $\pi:\mathbb{F}_{2^n}\to\mathbb{F}_2$. The function

$$
f(x)=\pi\Bigl(\sum_{|I|=t}\ \prod_{i\in I}\varphi_i(x)^{1+2+\cdots+2^{i}}\Bigr)
$$

is computable in time polynomial in $N$ and is an affine disperser for dimension $6N^{4/5}$: it is nonconstant on every affine subspace of $\{0,1\}^N$ of dimension greater than $6N^{4/5}$, for all sufficiently large $N$. Since $6N^{4/5}\le N/\log_2 N$ for large $N$, it is in particular an explicit affine disperser for dimension $O(N/\log N)$.

## Proof sketch

By Bertrand's postulate $n\le 4N^{3/5}$, so $r(r+1)/t\le r(r+1)\le N^{3/5}<n$, and $nr/t+nt+r(r+1)\le(4/\sqrt2+4/\sqrt2+1/4+o(1))N^{4/5}<6N^{4/5}$. Up to renaming the variables (and taking the trace form of $\pi$), $f$ is the function of the Ben-Sasson–Kopparty theorem with these parameters, which therefore applies. The elementary symmetric polynomial is evaluated with the Newton–Girard identities.

## Depends on

- [Ben-Sasson–Kopparty: the trace of an elementary symmetric polynomial is an affine disperser](ben-sasson-kopparty-trace-disperser.md)

## Sources

- E. Ben-Sasson and S. Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing 41(4), 880–914, 2012, Theorem 2.2 (case $p=2$) and its derivation from Theorem 7.3.
