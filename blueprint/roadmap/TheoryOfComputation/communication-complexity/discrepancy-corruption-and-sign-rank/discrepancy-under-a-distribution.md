# Discrepancy of a function under a distribution

Let $X$, $Y$ be finite nonempty sets, $f : X \times Y \to \{0,1\}$ and $\nu$ a probability distribution on $X \times Y$. The *discrepancy* of $f$ under $\nu$ is

$$\mathrm{disc}_\nu(f) = \max_{A \subseteq X,\ B \subseteq Y} \Big| \sum_{(x,y) \in A \times B} \nu(x,y)\, (-1)^{f(x,y)} \Big|,$$

and $\mathrm{disc}(f) = \min_\nu \mathrm{disc}_\nu(f)$. The *uniform discrepancy* $\mathrm{disc}_{\mathrm{unif}}(f)$ is $\mathrm{disc}_\nu(f)$ for $\nu$ uniform on $X \times Y$; it is the notion used by gadget-based lifting, and it can be much larger than $\mathrm{disc}(f)$. A protocol of cost $c$ with error at most $1/2 - \gamma$ under $\nu$ satisfies $2\gamma \le 2^c \mathrm{disc}_\nu(f)$, so $R_{1/2 - \gamma}(f) \ge \log_2 (2\gamma / \mathrm{disc}(f))$ for $0 < \gamma \le 1/2$ (fix the public coins to get a deterministic protocol with error at most $1/2-\gamma$ under a minimizing $\nu$).

## Depends on

- [Discrepancy lower bound for inner product](../query-and-communication-measures/discrepancy-lower-bound-for-inner-product.md)
- [Distributional communication complexity](../randomized-communication-protocols/dist-complexity.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 1988.
