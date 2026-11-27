# Exact weighted counting through binary-digit polynomials

Let $F$ be a CSP instance with natural-number weights, and replace each weight $w$ by the polynomial $\sum_i b_i X^i \in \mathbb{N}[X]$ of its binary digits $w = \sum_i b_i 2^i$. The partition function computed over $\mathbb{N}[X]$ evaluates at $X = 2$ to the original weighted count. If the weights of relation $R$ have at most $b_R$ bits, this polynomial has degree at most $\sum_{(R,\bar v)\in F}(b_R - 1)$ and coefficient sum at most $|D|^{n} \prod_{(R,\bar v)\in F} b_R$ for $n=|\mathrm{vars}(F)|$, so every coefficient has bit length $O(n\log|D| + \sum \log b_R)$, logarithmic in the weight bit lengths.

## Proof sketch

Evaluation at $2$ is a semiring homomorphism $\mathbb{N}[X] \to \mathbb{N}$, so it commutes with the partition function; degrees add across products and coefficient sums are bounded by evaluation at $X = 1$.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)

## Proof depends on

- [Algebraic laws and separator conditioning for partition functions](partition-function-separator-conditioning.md)

## Sources

- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
