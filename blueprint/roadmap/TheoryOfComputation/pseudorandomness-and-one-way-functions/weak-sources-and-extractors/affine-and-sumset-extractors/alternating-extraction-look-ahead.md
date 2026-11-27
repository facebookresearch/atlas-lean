# Alternating extraction with imperfect seeds and its look-ahead property

(Imperfect seeds.) If $\mathrm{Ext}$ is a strong $(k, \varepsilon)$-extractor, $X$ is a $k$-source and the seed $S$ is independent of $X$ and $\eta$-close to uniform, then $\mathrm{Ext}(X, S)$ is $(\eta + \varepsilon)$-close to uniform jointly with any side information determining $S$; if $S$ only has min-entropy $k_S$, the error is at most $|\Sigma|\,2^{-k_S}\varepsilon$.

(Alternating extraction.) Given strong extractors $\mathrm{Ext}_1$ (source $X$) and $\mathrm{Ext}_2$ (source $Y$), set $R_i = \mathrm{Ext}_1(X, S_i)$ and $S_{i+1} = \mathrm{Ext}_2(Y, R_i)$ from an initial seed $S_0$ taken from $Y$'s side. For independent $(X, X')$ and $(Y, Y', S_0, S'_0)$, where primed variables are tampered copies run on the same protocol, if each extractor has error $\varepsilon_1, \varepsilon_2$, $S_0$ is $\eta_0$-close to uniform given the $Y$-side, and the sources retain min-entropy up to $\delta$ losses, then $R_k$ is within $\eta_0 + (k+1)\varepsilon_1 + k\varepsilon_2 + (2k+2)\delta$ of uniform jointly with $(Y, Y', S_0, S'_0, R_0, \dots, R_{k-1}, R'_0, \dots, R'_k)$. The same holds on sumsets $A + B$ when both extractors are $\mathbb{F}_2$-linear in the source.

## Proof sketch

For imperfect seeds, replace $S$ by a uniform seed at cost $\eta$; for weak seeds, a uniform seed dominates up to the factor $|\Sigma|2^{-k_S}$. For alternation, condition round by round on the transcript of the passive source; by the chain rule the active source keeps enough min-entropy, and each extraction step adds its error.

## Depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)
- [Pointwise min-entropy chain rule and uniform lifting](../pointwise-min-entropy-chain-rule.md)

## Sources

- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics, 2019.
- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data", SIAM Journal on Computing, 2008.
