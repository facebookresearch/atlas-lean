# Low-discrepancy gadgets extract from independent min-entropy sources

Let $g : X \times Y \to \{0,1\}$ have uniform discrepancy at most $\gamma$, and let $P$ on $X$ and $Q$ on $Y$ be independent distributions with min-entropies $k_1$ and $k_2$ (every atom has mass at most $2^{-k_1}$, resp. $2^{-k_2}$). Then

$$\big| \mathbb{E}_{x \sim P,\, y \sim Q} (-1)^{g(x,y)} \big| \le \gamma \cdot \frac{|X|\,|Y|}{2^{k_1 + k_2}}.$$

In particular, if $\mathrm{disc}(g) \le |X|^{-\eta}$ with $|X| = |Y| = m$, then $g$ is a two-source extractor for min-entropy rates above $1 - \eta/2$.

## Proof sketch

The bilinear form $p^{\mathsf T} S q$ is linear in each of $p$ and $q$, so its extremes over the polytopes of distributions with atoms at most $2^{-k}$ are attained at scaled indicator vectors of sets, where the discrepancy bound applies; an elementary argument handles non-integral min-entropies.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021.
- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 1988.
