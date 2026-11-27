# The BNS–Chung cube bound on multiparty discrepancy

For $a, b \in \prod_i X_i$ and $S \subseteq [k]$ let $c_S(a, b)$ agree with $b$ on $S$ and with $a$ elsewhere. The *cube expectation* of $f$ is

$$\mathcal{E}(f) = \mathbb{E}_{a, b} \prod_{S \subseteq [k]} (-1)^{f(c_S(a,b))},$$

with $a, b$ independent and uniform. For $k \ge 1$, the uniform multiparty discrepancy satisfies $\mathrm{disc}^k(f)^{2^k} \le \mathcal{E}(f)$.

## Proof sketch

Apply Cauchy–Schwarz $k$ times, once per direction: each application duplicates one coordinate and removes the indicator of one cylinder, which does not depend on that coordinate. After $k$ steps all cylinder indicators are gone and the cube expectation remains.

## Depends on

- [Multiparty discrepancy](multiparty-discrepancy.md)

## Sources

- L. Babai, N. Nisan and M. Szegedy, "Multiparty Protocols, Pseudorandom Generators for Logspace, and Time-Space Trade-offs", Journal of Computer and System Sciences 45(2), 1992.
- F. R. K. Chung, "Quasi-Random Classes of Hypergraphs", Random Structures & Algorithms 1(4), 1990.
- R. Raz, "The BNS-Chung Criterion for Multi-Party Communication Complexity", Computational Complexity 9(2), 2000.
