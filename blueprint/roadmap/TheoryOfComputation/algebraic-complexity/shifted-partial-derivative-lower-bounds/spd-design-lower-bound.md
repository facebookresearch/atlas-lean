# Shifted partials of design polynomials are near-maximal

Let $F_{t,n} = \mathrm{NW}_{n,n,k}$ be the Nisan-Wigderson design polynomial of degree $n$ in $N = n^2$ variables $\{x_{i,j}\}_{i,j \in \mathbb{F}_n}$ (where $n$ is a prime power) with $k = \lfloor n/(2t) \rfloor$. Because distinct degree-$< k$ polynomials over $\mathbb{F}_n$ agree on fewer than $k$ points, every $k'$-th order partial derivative along design variables for $k' \le d - k$ (here $d = n$, in particular $k' = k$) is either zero or a single monomial, and the space $\langle \partial^{=k} F_{t,n} \rangle_{\le \ell}$ of shifted partials of shift degree at most $\ell$ is spanned precisely by all monomials of degree at most $\ell + n - k$ divisible by at least $n - k$ variables from some graph $S_a$ with $\deg a < k$ (Kayal–Saha–Saptharishi, Propositions 7–8). Moreover, whenever $\log^2 n < t < n/100$ and $\ell = \lceil c n^2 t / \log n \rceil$ for a constant $c > 5$, the shifted-partials dimension is nearly maximal up to a $(1 - o(1))/n^2$ factor of the ambient monomial space:

$$
\dim\bigl(\langle \partial^{=k} F_{t,n} \rangle_{\le \ell}\bigr) \;\ge\; \frac{1 - o(1)}{n^2} \binom{n^2 + \ell + n - k}{n^2}.
$$

## Proof sketch

Distinct degree-$<k$ polynomials $a \in \mathbb{F}_n[z]$ give graphs $S_a \subseteq \mathbb{F}_n^2$ that pairwise share fewer than $k$ points, so every $k$-th order partial derivative of $F_{t,n}$ is zero or a single monomial of degree $n - k$, and shifting by monomials of degree at most $\ell$ yields precisely the monomials of degree at most $\ell + n - k$ containing at least $n - k$ variables from some $S_a$ (Propositions 7–8). Estimating the probability that a uniformly random monomial of degree at most $\ell + n - k$ misses at most $k$ variables of some $S_a$ via a second-moment argument (Lemma 9) shows that at least a $(1 - o(1))/n^2$ fraction of all monomials of degree at most $\ell + n - k$ lie in the span.

## Depends on

- [Projected shifted partials and the Nisan–Wigderson design polynomial](projected-shifted-partials.md)
- [The dimension of shifted partial derivatives](shifted-partials-measure.md)

## Sources

- N. Kayal, C. Saha, R. Saptharishi, "A super-polynomial lower bound for regular arithmetic formulas", STOC (2014), ECCC TR13-091 (Propositions 7–8 and Lemma 9).
