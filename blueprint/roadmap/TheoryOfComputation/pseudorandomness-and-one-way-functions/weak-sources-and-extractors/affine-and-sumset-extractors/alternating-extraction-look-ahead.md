# Look-ahead property of alternating extraction

Let $\mathrm{Ext}_1$ (applied to $X$) and $\mathrm{Ext}_2$ (applied to $Q$) be strong $(k, \varepsilon)$-extractors with $s$-bit seeds and $s$-bit outputs. With $Y = (Q, S_0)$ for a uniform $s$-bit $S_0$, set $R_i = \mathrm{Ext}_1(X, S_i)$ and $S_{i+1} = \mathrm{Ext}_2(Q, R_i)$ for $0 \le i < \ell$. Let $X'$ be arbitrarily correlated with $X$ and $Y' = (Q', S'_0)$ arbitrarily correlated with $Y$ (tampered copies, run through the same steps to give $R'_i$), with $(X, X')$ independent of $(Y, Y')$. If $H_\infty(X), H_\infty(Q) \ge k + 2\ell s + 2\log_2(1/\varepsilon)$, then for every $0 \le i < \ell$ the block $R_i$ is $O(\ell\varepsilon)$-close to uniform jointly with $(Y, Y', R_0, R'_0, \dots, R_{i-1}, R'_{i-1})$; the tampered block $R'_i$ of the same round is not included.

## Proof sketch

Condition round by round on the blocks already produced; each block has at most $s$ bits, so by the chain rule for average min-entropy each source keeps min-entropy $k + 2\log_2(1/\varepsilon)$ after the at most $2\ell$ blocks of both copies are fixed, and each extraction step adds $O(\varepsilon)$.

Derived extensions (stated in none of the cited sources):

- Imperfect seeds. If $S$ is independent of the $k$-source $X$ and $\eta$-close to uniform, then $\mathrm{Ext}_1(X, S)$ is $(\eta + \varepsilon)$-close to uniform jointly with any side information $Z$ that determines $S$ and is independent of $X$ (replace $S$ by a uniform seed at cost $\eta$); if $S$ ranges over a set $\Sigma$ and only has min-entropy $k_S$, the error is at most $|\Sigma|\,2^{-k_S}\varepsilon$ (a uniform seed dominates up to that factor).
- If $S_0$ is only $\eta_0$-close to uniform given $Q$, the look-ahead error grows by $\eta_0$; and the look-ahead property holds on sumsets $A + B$ when both extractors are $\mathbb{F}_2$-linear in the source.

## Depends on

- [Seeded randomness extractors](../seeded-randomness-extractors.md)
- [k-sources, (k, ε)-sources and flat sources](../weak-random-sources.md)

## Proof depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)
- [Min-entropy chain rule for conditioning on a variable with few values](../pointwise-min-entropy-chain-rule.md)

## Sources

- X. Li and Y. Zhong, "Explicit Directional Affine Extractors and Improved Hardness for Linear Branching Programs", Proceedings of the 39th Computational Complexity Conference (CCC 2024), numbering of arXiv:2304.11495v2, Definition 18 and Lemma 14 (look-ahead extractor, citing Chattopadhyay–Goyal–Li).
- E. Chattopadhyay, V. Goyal and X. Li, "Non-Malleable Extractors and Codes, with their Many Tampered Extensions", Proceedings of the 48th ACM Symposium on Theory of Computing (STOC 2016), 285–298, 2016 (look-ahead extractor).
- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019.
- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data", SIAM Journal on Computing 38(1), 97–139, 2008, Lemma 2.2 (average min-entropy chain rule).
