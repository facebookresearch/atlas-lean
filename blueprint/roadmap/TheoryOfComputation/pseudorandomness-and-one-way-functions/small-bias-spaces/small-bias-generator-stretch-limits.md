# Stretch limits for low-degree and linear small-bias generators

Let $G : \{0,1\}^k \to \{0,1\}^\ell$ be $\varepsilon$-biased under a uniform seed with $\varepsilon < 1$. If every output bit is an $\mathbb{F}_2$-polynomial of total degree at most $d$ in the seed bits, then $\ell \le \sum_{i=1}^d \binom{k}{i}$. Consequently, for any finite seed set $\sigma$ an $\varepsilon$-biased sample space with $\varepsilon < 1$ has $\ell < |\sigma|$ (so $\ell < 2^k$), and no $\mathbb{F}_2$-linear map $G$ with $\ell > k$ is $\varepsilon$-biased.

## Proof sketch

If the output bits, minus constants, lie in a space $W$ of functions of the seed with $\dim W < \ell$, some nonempty set of outputs sums to a constant, giving bias $\pm 1$. Polynomials of degree at most $d$ without constant term span a space of dimension $\sum_{i=1}^d \binom{k}{i}$; functions vanishing at a fixed seed span dimension $|\sigma| - 1$.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 8.37 and its two corollaries (numbering of the 2007 public draft; bias there is $|\Pr[0]-\Pr[1]|$ as here).
