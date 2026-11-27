# Seeded randomness extractors

Let $\mathrm{Ext} : \Omega \times \Sigma \to \Theta$ with $\Sigma, \Theta$ finite. $\mathrm{Ext}$ is a *$(k, \varepsilon)$-extractor* if for every $k$-source $X$ on $\Omega$ and a seed $S$ uniform on $\Sigma$ independent of $X$, the distribution of $\mathrm{Ext}(X, S)$ is within statistical distance $\varepsilon$ of uniform on $\Theta$. It is *strong* if $(S, \mathrm{Ext}(X, S))$ is $\varepsilon$-close to uniform on $\Sigma \times \Theta$. Every strong $(k,\varepsilon)$-extractor is a $(k,\varepsilon)$-extractor, and either notion applied to a $(k, \delta)$-source gives error at most $\varepsilon + \delta$.

## Depends on

- [k-sources, (k, ε)-sources and flat sources](weak-random-sources.md)
- [Leftover hash lemma as a strong extractor](../derandomization/leftover-hash-lemma-as-a-strong-extractor.md)

## Sources

- N. Nisan and D. Zuckerman, "Randomness is Linear in Space", Journal of Computer and System Sciences 52(1), 43–52, 1996.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012, Definitions 6.13 and 6.16.
