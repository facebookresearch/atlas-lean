# Two-source extractors

A function $\mathrm{Ext} : \mathcal{X} \times \mathcal{Y} \to \Theta$ on finite sets is a *$(k_1, k_2, \varepsilon)$ two-source extractor* if for all independent sources $X$ on $\mathcal{X}$ and $Y$ on $\mathcal{Y}$ with min-entropy at least $k_1$ and $k_2$, the distribution of $\mathrm{Ext}(X, Y)$ is within statistical distance $\varepsilon$ of uniform on $\Theta$. It is *strong in the second source* if $(Y, \mathrm{Ext}(X,Y))$ is $\varepsilon$-close to $(Y, U_\Theta)$ with $U_\Theta$ uniform and independent. A strong two-source extractor is a two-source extractor.

## Depends on

- [k-sources, (k, ε)-sources and flat sources](weak-random-sources.md)

## Sources

- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 230–261, 1988.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012, Section 8.2 (extractors for independent sources).
