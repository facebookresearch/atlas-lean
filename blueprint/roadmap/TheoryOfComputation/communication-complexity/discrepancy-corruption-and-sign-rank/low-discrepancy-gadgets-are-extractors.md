# Low-discrepancy gadgets extract from independent min-entropy sources

Let $g : X \times Y \to \{0,1\}$ have uniform discrepancy $\mathrm{disc}_{\mathrm{unif}}(g) \le \gamma$, and let $P$ on $X$ and $Q$ on $Y$ be independent distributions with min-entropies $k_1$ and $k_2$ (every atom has mass at most $2^{-k_1}$, resp. $2^{-k_2}$). Then

$$\big| \mathbb{E}_{x \sim P,\, y \sim Q} (-1)^{g(x,y)} \big| \le \gamma \cdot \frac{|X|\,|Y|}{2^{k_1 + k_2}}.$$

In particular, if $|X| = |Y| = m$ and $\mathrm{disc}_{\mathrm{unif}}(g) \le m^{-\eta}$, then $k_1 + k_2 \ge (2 - \eta + \lambda)\log_2 m$ gives bias at most $m^{-\lambda}$; for instance min-entropy rates $k_i/\log_2 m \ge 1 - \eta/2 + \delta$ give bias at most $m^{-2\delta}$. The uniform discrepancy is essential here: a bound on the minimum-over-distributions discrepancy $\mathrm{disc}(g)$ does not suffice (an inner-product block on one quarter of $X \times Y$ and the constant $0$ elsewhere has small discrepancy under the uniform distribution on that block, yet sources supported on the complementary halves have entropy $\log_2 m - 1$ and constant output).

## Proof sketch

Write $p = 2^{-k_1} a$ and $q = 2^{-k_2} b$ with $a \in [0,1]^X$, $b \in [0,1]^Y$. The bilinear form $a^{\mathsf T} S b$ in the sign matrix $S$ is linear in each argument, so its maximum absolute value over the box $[0,1]^X \times [0,1]^Y$ is attained at $0/1$ vectors, i.e. indicators of a rectangle, where it is at most $\gamma |X| |Y|$.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)
- [k-sources, (k, ε)-sources and flat sources](../../pseudorandomness-and-one-way-functions/weak-sources-and-extractors/weak-random-sources.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021 (Definition 1.1, uniform discrepancy, and Lemma 2.9).
- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 1988.
