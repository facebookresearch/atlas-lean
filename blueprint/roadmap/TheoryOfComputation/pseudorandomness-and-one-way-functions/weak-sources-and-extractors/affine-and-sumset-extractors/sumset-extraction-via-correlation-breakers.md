# Linear extractors and weak-seed correlation breakers reduce sumset extraction to resilient functions

A *strong $t$-affine correlation breaker with advice* for entropy $k$ and error $\varepsilon_{CB}$ is $\mathrm{CB} : \{0,1\}^n \times \{0,1\}^d \times \{0,1\}^a \to \{0,1\}^m$ such that for all distributions $X = A + B$, $Y, Y_1, \dots, Y_t$ and advice strings $\alpha, \alpha_1, \dots, \alpha_t$ with $H_\infty(A) \ge k$, $Y$ uniform, $A$ independent of $(B, Y, Y_1, \dots, Y_t)$ and $\alpha_i \ne \alpha$ for all $i$, the output $\mathrm{CB}(X, Y, \alpha)$ is $\varepsilon_{CB}$-close to uniform jointly with $Y$ and all $(Y_i, \mathrm{CB}(X, Y_i, \alpha_i))$. For $t = 0$ and $m = 1$ the inner product $\mathrm{CB}(x, y) = \langle x, y\rangle$ with $d = n$ is an example: given $B$ and $Y$, $\langle A + B, Y\rangle = \langle A, Y\rangle + \langle B, Y\rangle$, and the Chor–Goldreich bound applies to $A$ and the uniform $Y$.

(Bad seeds under leakage.) Let $\mathrm{CB}$ be as above, $L : \{0,1\}^n \times \{0,1\}^a \to \{0,1\}^d$ any function of the source (the *leakage*, for instance a linear seeded extractor $\mathrm{LExt}(x, \cdot)$ evaluated at the advice), $\alpha \ne \alpha_1, \dots, \alpha_t$ fixed, and $A$ a source of min-entropy $k + (t+1)d$. Call $y$ *bad* if for some shift $b$ and some $y_1, \dots, y_t$ the bit $\mathrm{CB}(A + b, y + L(A, \alpha), \alpha)$ is not $\gamma$-close to uniform given the outputs $\mathrm{CB}(A + b, y_i + L(A, \alpha_i), \alpha_i)$. Then a uniform $y$ is bad with probability at most $\varepsilon_{CB}/\gamma$.

(Reduction.) Evaluating such a correlation breaker on seeds produced from the source itself by a linear somewhere-random sampler, with the advice indexing the table position, maps every sum $X = X_1 + X_2$ of independent sources of large enough min-entropy to a distribution close to a convex combination of $(q, t)$-non-oblivious bit-fixing sources with $q$ a small fraction of the table length. Composing with a function that extracts from such sources (a resilient function of small bias under $t$-wise independent distributions) gives an explicit extractor for the sum of two independent sources, down to min-entropy $O(\log n)$ for constant error.

## Proof sketch

Bad seeds: if bad seeds had probability $\delta > \varepsilon_{CB}/\gamma$, choose for each bad $y$ witnesses $b = g(y)$ and $y_i = f_i(y)$, and set $Y = W + L(A, \alpha)$, $Y_i = W + L(A, \alpha_i)$, $B = g(W)$ for uniform $W$. With $Z = (L(A, \alpha), L(A, \alpha_1), \dots)$, $A$ keeps average min-entropy $k$ given $Z$, $Y$ is uniform given $Z$, and $A \leftrightarrow Z \leftrightarrow (B, Y, Y_1, \dots, Y_t)$ is a Markov chain, so the correlation-breaker guarantee gives error at most $\varepsilon_{CB}$, while the bad seeds force error at least $\gamma\delta$. Reduction: by linearity the sampler output on $X_1 + X_2$ is the sampled $X_1$-part shifted by an $X_2$-dependent leakage; outside the few bad table positions, which form the coalition, every $t$ outputs are almost uniform, and the smoothing lemma turns almost $t$-wise independence into a nearby $t$-wise independent distribution.

## Depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)
- [Coalition influence and resilient functions](../resilient-functions.md)
- [Fourier extraction from sumsets and the bent inner-product sumset extractor](fourier-sumset-extraction.md)

## Proof depends on

- [Resilient functions extract from non-oblivious bit-fixing sources](../resilient-functions-extract-from-nobf-sources.md)
- [Inner-product extraction above half entropy and the half-entropy barrier](../../non-malleable-extraction-and-explicit-ramsey-graphs/chor-goldreich-inner-product-extractor-and-half-entropy-barrier.md)

## Sources

- E. Chattopadhyay and J.-J. Liao, "Extractors for Sum of Two Sources", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC 2022), 1584–1597, 2022, Definitions 1.8 and 5.2, Lemmas 5.3 and 5.4, Theorems 1 and 2 (arXiv:2110.12652).
- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023 (numbering of arXiv:2303.06802), Definition 3.4 and Theorems 7.11–7.13.
- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019 (numbering of ECCC TR15-119), Lemma 2.11.
- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 230–261, 1988.
