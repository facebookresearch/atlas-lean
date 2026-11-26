# Chattopadhyay–Zuckerman: resilient functions and non-malleable extractors give two-source extractors

A function $\mathrm{nmExt} : \mathcal{X} \times \Sigma \times [D] \to \{0,1\}$ is a *$t$-non-malleable extractor with advice* for $k$-sources with error $\varepsilon_{nm}$ if for every $k$-source $X$, uniform seed $S$, advice $\alpha$ and tampering functions $A_1, \dots, A_t$ producing seeds and advice $(S'_j, \alpha'_j)$ with $\alpha'_j \ne \alpha$, the bit $\mathrm{nmExt}(X, S, \alpha)$ is $\varepsilon_{nm}$-close to uniform jointly with $S$ and all tampered outputs; for $t = 0$ this is a family of strong seeded extractors.

Let $\mathrm{cond} : \mathcal{Y} \times [D] \to \Sigma$ be a seeded condenser such that for every $k_2$-source $Y$ at most $q$ seeds $i$ are bad and outside them $\mathrm{cond}(Y, i)$ has min-entropy deficiency at most $\Delta$ (up to error $\gamma$), and let $f : \{0,1\}^D \to \{0,1\}$ be $(t+1)$-independent $(q, \varepsilon_{res})$-resilient with bias at most $\varepsilon_{bias}$ under $(t+1)$-wise independent distributions. Then $(x, y) \mapsto f\bigl((\mathrm{nmExt}(x, \mathrm{cond}(y, i), i))_{i \in [D]}\bigr)$ is a two-source extractor with error at most $\varepsilon_{bias} + \varepsilon_{res} + D^{t+1}(2\gamma + 2^{\Delta+1}\varepsilon_{nm})$.

## Proof sketch

Fix $Y$ and drop its bad seeds as a coalition. Conditioned on the good seeds, non-malleability with advice $i$ against the $t$ other coordinates makes the table $(\mathrm{nmExt}(X, \mathrm{cond}(Y,i), i))_i$ restricted to good coordinates $(t+1)$-wise $(2\gamma + 2^{\Delta+1}\varepsilon_{nm})$-biased, the factor $2^{\Delta}$ paying for the entropy deficiency of the seed. The bad coordinates form a non-oblivious coalition, and resilient extraction finishes.

## Depends on

- [Two-source extractors](two-source-extractors.md)
- [Resilient functions extract from non-oblivious bit-fixing sources](resilient-functions-extract-from-nobf-sources.md)
- [Seeded randomness extractors](seeded-randomness-extractors.md)

## Proof depends on

- [Resilient functions extract from non-oblivious bit-fixing sources](resilient-functions-extract-from-nobf-sources.md)

## Sources

- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics, 2019.
