# An explicit polynomial-time affine disperser for dimension O(N^{4/5})

There is a family $f_N:\{0,1\}^{N}\to\{0,1\}$, computable in time polynomial in $N$, such that $f_N$ is an affine disperser for every dimension greater than $6N^{4/5}$. Concretely, let $n$ be the smallest prime larger than $2N^{3/5}$, $r=\lceil N/n\rceil$ and $t=\lceil\sqrt r\rceil$; let $\varphi=(\varphi_1,\dots,\varphi_r):\mathbb{F}_2^N\to(\mathbb{F}_{2^n})^r$ be an injective $\mathbb{F}_2$-linear map and $\pi:\mathbb{F}_{2^n}\to\mathbb{F}_2$ a nonzero $\mathbb{F}_2$-linear map. Then

$$
f_N(x)=\pi\Bigl(\mathrm{Sym}_t\bigl(\varphi_1(x)^{1+2},\ \varphi_2(x)^{1+2+2^2},\ \dots,\ \varphi_r(x)^{1+2+\cdots+2^r}\bigr)\Bigr),
$$

where $\mathrm{Sym}_t$ is the $t$-th elementary symmetric polynomial. Arithmetic in $\mathbb{F}_{2^n}$ is made explicit by an irreducible polynomial of degree $n$ over $\mathbb{F}_2$ found deterministically in polynomial time, and $\mathrm{Sym}_t$ is evaluated with the Newton–Girard identities.

## Proof sketch

Ben-Sasson and Kopparty derive Theorem 2.2 from their trace-disperser theorem (Theorem 7.3); every nonzero $\mathbb{F}_2$-linear $\pi$ has the form $z\mapsto\mathrm{Tr}(\mu z)$ with $\mu\ne0$. They show that if $f_N$ were constant on an affine subspace of dimension above $6N^{4/5}$, then, after a change of variables, a sum of products of subspace polynomials restricted to that space would have too many roots for its degree; their main structural lemma on images of subspace polynomials rules this out. Explicitness follows from Shoup's deterministic construction of the irreducible polynomial.

## Depends on

- [Affine dispersers](../gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)

## Proof depends on

- [Ben-Sasson–Kopparty: the trace of an elementary symmetric polynomial is an affine disperser](../../../../pseudorandomness-and-one-way-functions/weak-sources-and-extractors/affine-dispersers/ben-sasson-kopparty-trace-disperser.md)
- [Shoup: deterministic construction of irreducible polynomials over GF(2)](../../../../polynomial-time-problems/exact-algebraic-and-combinatorial-algorithms/shoup-irreducible-polynomials.md)

## Sources

- Eli Ben-Sasson and Swastik Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing 41(4), 880–914, 2012 (Theorem 2.2, with $p=2$ and $m=N$).
- Victor Shoup, "New Algorithms for Finding Irreducible Polynomials over Finite Fields", Mathematics of Computation 54(189), 435–447, 1990.
