# Linear extractors and weak-seed correlation breakers reduce sumset extraction to resilient functions

A *linear weak-seed $t$-correlation breaker with advice* is $\mathrm{CB} : \{0,1\}^n \times \{0,1\}^m \times \mathcal{A} \to \{0,1\}$, $\mathbb{F}_2$-linear in its source, such that for an independent source $B$ and weak seed $Y$, $\mathrm{CB}(B, Y, \alpha)$ is $\varepsilon_{CB}$-close to uniform jointly with up to $t$ tampered outputs $\mathrm{CB}(B, Y'_j, \alpha'_j)$ with $\alpha'_j \ne \alpha$. Examples: the inner product ($t = 0$, via Chor–Goldreich) and block inner products on disjoint blocks, or a Vandermonde polynomial evaluation over $\mathbb{F}_{2^{\ell}}$ using $(t+1)\ell$ source bits, for arbitrary $t$ at high source entropy.

Given a linear strong extractor $\mathrm{LExt}$ and such a $\mathrm{CB}$, the table $T(x)_s = \mathrm{CB}(x, \mathrm{LExt}(x, s), s)$ over seeds $s$, evaluated on a sumset $A + B$, is, outside a bad set of seeds of density at most $\varepsilon_1/\gamma$, $(t+1)$-wise $2(2\gamma + \delta_A + \delta_B + \varepsilon_{CB})$-biased. Composing with a function $R$ of bounded bias and coalition influence under such distributions gives a sumset extractor.

## Proof sketch

By linearity, $\mathrm{LExt}(A+B, s) = \mathrm{LExt}(A, s) + \mathrm{LExt}(B, s)$ is close to uniform even given $B$ for good seeds (Markov's inequality bounds the bad ones). The correlation breaker, applied with advice $s$ and the extracted weak seed, decorrelates each good coordinate from any $t$ others; this gives the $(t+1)$-wise small bias, and non-oblivious bit-fixing extraction with the bad seeds as coalition completes the reduction.

## Depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)
- [Coalition influence and resilient functions](../resilient-functions.md)
- [Fourier extraction from sumsets and the bent inner-product sumset extractor](fourier-sumset-extraction.md)

## Proof depends on

- [Resilient functions extract from non-oblivious bit-fixing sources](../resilient-functions-extract-from-nobf-sources.md)
- [Chor–Goldreich: the inner product extracts from two weak sources](../chor-goldreich-inner-product-extractor.md)

## Sources

- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics, 2019.
- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing, 1988.
