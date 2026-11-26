# Chor–Goldreich: the inner product extracts from two weak sources

Let $n \ge 1$ and let $X, Y$ be independent distributions on $\{0,1\}^n$ with real min-entropies at least $k_1$ and $k_2$. Then the inner product $\langle X, Y\rangle \bmod 2$ satisfies

$$
\mathbb{E}_{y \sim Y}\bigl|\mathbb{E}_{x \sim X}(-1)^{\langle x, y\rangle}\bigr| \le 2^{(n - k_1 - k_2)/2},
$$

so $(Y, \langle X, Y\rangle)$ is within statistical distance $2^{(n-k_1-k_2)/2}/2$ of $(Y, U_1)$: the inner product is a strong two-source extractor with error $\tfrac12 2^{(n-k_1-k_2)/2}$, below $1/2$ once $k_1 + k_2 > n$. The threshold cannot be lowered to $k_1 + k_2 = n$: for a coordinate set $T$, uniform strings supported on $T$ and uniform strings supported on its complement have min-entropies $|T|$ and $n - |T|$, yet their inner product is constantly $0$.

## Proof sketch

The distance of a bit from uniform is half its bias. For fixed $y$, the bias of $\langle x, y\rangle$ is the Hadamard transform of the mass function $p$ of $X$ at $y$. Cauchy–Schwarz over $y$ weighted by $q$ and Parseval give an average bias at most $\sqrt{2^n\|p\|_2^2\|q\|_2^2}$, and a $k$-source has $\|p\|_2^2 \le 2^{-k}$.

## Depends on

- [Two-source extractors](two-source-extractors.md)
- [Inner product of bit strings modulo two](../../../ComputerScience/quantum-algorithms/deutsch-jozsa-and-bernstein-vazirani-algorithms/bit-dot.md)
- [Parseval's identity on the Boolean cube](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-parseval.md)

## Sources

- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing, 1988.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
