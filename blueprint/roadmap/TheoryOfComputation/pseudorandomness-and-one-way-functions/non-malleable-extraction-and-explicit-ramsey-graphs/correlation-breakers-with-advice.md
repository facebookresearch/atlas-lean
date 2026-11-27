# Correlation breakers with advice

A function $\mathrm{AdvCB} : \{0,1\}^n \times \{0,1\}^d \times \{0,1\}^a \to \{0,1\}^m$ is a **strong $(k, \varepsilon)$ correlation breaker with advice** (Cohen, Definitions 1.1 and 6.1; Li, Definition 3.3) if for every $(n, k)$-source $X$ (i.e. $H_\infty(X) \ge k$) arbitrarily correlated with an $n$-bit random variable $X'$, every pair of (possibly correlated) seeds $Y, Y'$ with $Y$ uniform on $\{0,1\}^d$ and $(Y, Y')$ independent of $(X, X')$, and every pair of distinct advice strings $\alpha \ne \alpha'$,

$$
\big(\mathrm{AdvCB}(X, Y, \alpha),\ \mathrm{AdvCB}(X', Y', \alpha'),\ Y, Y'\big) \approx_\varepsilon \big(U_m,\ \mathrm{AdvCB}(X', Y', \alpha'),\ Y, Y'\big).
$$

(The standard non-strong variant omits $(Y, Y')$ from both sides of the statistical closeness.) Combined with an *advice generator* producing, from $(X, Y)$, a short string guaranteed (with high probability) to differ under tampering, it yields non-malleable extractors.

## Depends on

- [Seeded non-malleable extractors (Dodis-Wichs)](seeded-non-malleable-extractors.md)

## Sources

- Gil Cohen, "Making the most of advice: new correlation breakers and their applications", FOCS (2016).
- Xin Li, "Two source extractors for asymptotically optimal entropy, and (many) more", FOCS (2023); arXiv:2303.06802.
