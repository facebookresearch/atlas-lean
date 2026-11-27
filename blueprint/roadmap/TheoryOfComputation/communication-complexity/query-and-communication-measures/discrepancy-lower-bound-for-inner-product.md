# Discrepancy lower bound for inner product

For $g : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ and a set $S$ of inputs, the *discrepancy* of $S$ with respect to $g$ is
$\left| \mathbb{E}_{x,y}\left[\chi_S(x, y)\,(-1)^{g(x,y)}\right] \right|$, the expectation over uniform inputs, that is, the difference between the measures
of $S \cap g^{-1}(0)$ and $S \cap g^{-1}(1)$.

- **Discrepancy bound.** If every rectangle $A \times B$ has discrepancy at most $\gamma$ with respect to $g$, then for every $0 \le \varepsilon < \frac12$, every deterministic protocol
  whose output equals $g$ except on an $\varepsilon$ fraction of uniformly random inputs communicates at least $\log_2 \frac{1 - 2\varepsilon}{\gamma}$ bits.
  The same bound holds, for the same range of $\varepsilon$, for public-coin protocols with error at most $\varepsilon$ on every input, since some fixing of the random string errs on
  at most an $\varepsilon$ fraction of inputs.
- **Inner product.** For $\mathrm{IP}_n(x, y) = \sum_i x_i y_i \bmod 2$, every rectangle has discrepancy at most $2^{-n/2}$.

Consequently any public-coin protocol computing $\mathrm{IP}_n$ with error at most $\frac13$ on every input communicates at least
$\frac n2 - \log_2 3$ bits, so the randomized communication complexity of $\mathrm{IP}_n$ is $\Omega(n)$.

## Depends on

- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity and Applications*, Cambridge University Press, 2020, draft <https://yehudayoff.net.technion.ac.il/files/2016/03/book.pdf>: Chapter 5 (definition of discrepancy, Fact 5.1, Theorem 5.2 and Lemma 5.5).
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Section 12.2.4 (discrepancy of the inner product via eigenvalues).
