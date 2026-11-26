# Correlation breakers with advice

A function $\mathrm{AdvCB} : \{0,1\}^n \times \{0,1\}^d \times \{0,1\}^a \to \{0,1\}^m$ is a *$(k, \varepsilon)$ correlation breaker with advice* if for every $X$ with $H_\infty(X) \ge k$, every pair of (possibly correlated) seeds $Y, Y'$ with $Y$ uniform and $(Y, Y')$ independent of $X$, and every pair of distinct advice strings $\alpha \ne \alpha'$,

$$
\big(\mathrm{AdvCB}(X, Y, \alpha),\ \mathrm{AdvCB}(X, Y', \alpha'),\ Y, Y'\big) \approx_\varepsilon \big(U_m,\ \mathrm{AdvCB}(X, Y', \alpha'),\ Y, Y'\big).
$$

Combined with an *advice generator* producing, from $(X, Y)$, a short string guaranteed (with high probability) to differ under tampering, it yields non-malleable extractors.

## Depends on

- [Seeded non-malleable extractors (Dodis-Wichs)](seeded-non-malleable-extractors.md)

## Sources

- Gil Cohen, "Making the most of advice: new correlation breakers and their applications", FOCS (2016).
- Xin Li, "Two source extractors for asymptotically optimal entropy, and (many) more", FOCS (2023); arXiv:2303.06802.
