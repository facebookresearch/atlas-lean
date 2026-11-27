# The online Kraft–Chaitin theorem

Let $(\ell_i)_{i \ge 0}$ be a computable, finite or infinite, sequence of requested codeword lengths satisfying $\sum_i 2^{-\ell_i} \le 1$. Then there is a computable sequence of pairwise prefix-incomparable binary strings $w_i$ with $|w_i| = \ell_i$, where $w_i$ is chosen at the time request $i$ arrives, without knowledge of later requests. Consequently any computably enumerable set of requests $(x, \ell)$ with total weight $\sum 2^{-\ell} \le 1$ is realized by a prefix-free machine $M$ with $K_M(x) \le \ell$ for each request.

## Proof sketch

Maintain the free part of $[0,1)$ as a finite set of dyadic intervals of distinct lengths (the binary expansion of the remaining measure). Serve a request of length $\ell$ from the shortest free interval of length at least $2^{-\ell}$, splitting it into its left part of length $2^{-\ell}$ and dyadic pieces of distinct lengths; the invariant ensures a suitable interval exists whenever the remaining measure is at least $2^{-\ell}$.

## Depends on

- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)
- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)

## Proof depends on

- [Kraft's inequality for prefix codes](../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
- G. J. Chaitin, "A Theory of Program Size Formally Identical to Information Theory", Journal of the ACM 22(3), 329–340, 1975, Theorem 3.2.
