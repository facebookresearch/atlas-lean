# Seeded non-malleable extractors (Dodis-Wichs)

A function $\mathrm{nmExt} : \{0,1\}^n \times \{0,1\}^d \to \{0,1\}^m$ is a *$(k, \varepsilon)$ seeded non-malleable extractor* if for every random variable $X$ on $\{0,1\}^n$ with min-entropy $H_\infty(X) \ge k$, independent uniform seed $Y$ on $\{0,1\}^d$, and every function $\mathcal{A} : \{0,1\}^d \to \{0,1\}^d$ without fixed points,

$$
\big(\mathrm{nmExt}(X, Y),\ \mathrm{nmExt}(X, \mathcal{A}(Y)),\ Y\big) \approx_\varepsilon \big(U_m,\ \mathrm{nmExt}(X, \mathcal{A}(Y)),\ Y\big),
$$

where $\approx_\varepsilon$ denotes statistical distance at most $\varepsilon$ and $U_m$ is uniform and independent of the rest. A $t$-non-malleable extractor allows $t$ tampering functions simultaneously.

## Depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)
- [Leftover hash lemma as a strong extractor](../derandomization/leftover-hash-lemma-as-a-strong-extractor.md)

## Sources

- Yevgeniy Dodis, Daniel Wichs, "Non-malleable extractors and symmetric key cryptography from weak secrets", STOC (2009).
- Eshan Chattopadhyay, David Zuckerman, "Explicit two-source extractors and resilient functions", Annals of Mathematics 189(3) (2019), STOC (2016); ECCC TR15-119.
