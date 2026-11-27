# Alternating extraction with imperfect seeds and its look-ahead property

(Imperfect seeds.) If $\mathrm{Ext}$ is a strong $(k, \varepsilon)$-extractor with seeds ranging over a set $\Sigma$, $X$ is a $k$-source and the seed $S$ is independent of $X$ and $\eta$-close to uniform, then $\mathrm{Ext}(X, S)$ is $(\eta + \varepsilon)$-close to uniform jointly with any side information $Z$ that determines $S$ and is independent of $X$; if $S$ only has min-entropy $k_S$, the error is at most $|\Sigma|\,2^{-k_S}\varepsilon$.

(Alternating extraction, look-ahead property.) Let $\mathrm{Ext}_1$ (applied to $X$) and $\mathrm{Ext}_2$ (applied to $Q$) be strong $(k, \varepsilon)$-extractors with $s$-bit seeds and $s$-bit outputs. With $Y = (Q, S_0)$ for a uniform $s$-bit $S_0$, set $R_i = \mathrm{Ext}_1(X, S_i)$ and $S_{i+1} = \mathrm{Ext}_2(Q, R_i)$ for $0 \le i < \ell$. Let $X'$ be arbitrarily correlated with $X$ and $Y' = (Q', S'_0)$ arbitrarily correlated with $Y$ (tampered copies, run through the same steps to give $R'_i$), with $(X, X')$ independent of $(Y, Y')$. If $H_\infty(X), H_\infty(Q) \ge k + 2\ell s + 2\log_2(1/\varepsilon)$, then for every $0 \le i < \ell$ the block $R_i$ is $O(\ell\varepsilon)$-close to uniform jointly with $(Y, Y', R_0, R'_0, \dots, R_{i-1}, R'_{i-1})$; the tampered block $R'_i$ of the same round is not included. If $S_0$ is only $\eta_0$-close to uniform given $Q$, the error grows by $\eta_0$. The same holds on sumsets $A + B$ when both extractors are $\mathbb{F}_2$-linear in the source.

## Proof sketch

For imperfect seeds, replace $S$ by a uniform seed at cost $\eta$; for weak seeds, a uniform seed dominates up to the factor $|\Sigma|2^{-k_S}$. For alternation, condition round by round on the blocks already produced; each block has at most $s$ bits, so by the chain rule for average min-entropy each source keeps min-entropy $k + 2\log_2(1/\varepsilon)$ after the at most $2\ell$ blocks of both copies are fixed, and each extraction step adds $O(\varepsilon)$.

## Depends on

- [F2-linear strong seeded extractors](linear-strong-seeded-extractors.md)

## Proof depends on

- [Pointwise min-entropy chain rule and uniform lifting](../pointwise-min-entropy-chain-rule.md)

## Sources

- E. Chattopadhyay, V. Goyal and X. Li, "Non-Malleable Extractors and Codes, with their Many Tampered Extensions", Proceedings of the 48th ACM Symposium on Theory of Computing (STOC 2016), 285–298, 2016 (look-ahead extractor, as restated in Li–Zhong, CCC 2024, Lemma 14).
- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019.
- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data", SIAM Journal on Computing 38(1), 97–139, 2008, Lemma 2.2 (average min-entropy chain rule).
