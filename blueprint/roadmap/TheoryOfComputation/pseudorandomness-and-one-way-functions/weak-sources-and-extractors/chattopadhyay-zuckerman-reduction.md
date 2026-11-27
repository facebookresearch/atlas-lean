# Chattopadhyay–Zuckerman: resilient functions and non-malleable extractors give two-source extractors

A distribution on $D$ bits is *$(t, \gamma)$-wise independent* if its restriction to any $t$ coordinates is $\gamma$-close to uniform, and a source $Z$ on $\{0,1\}^D$ is a *$(q, t, \gamma)$-non-oblivious bit-fixing source* if for some set $Q$ of at most $q$ coordinates the bits outside $Q$ are $(t, \gamma)$-wise independent, while the bits in $Q$ may depend arbitrarily on them. A function $\mathrm{nmExt} : \{0,1\}^n \times \{0,1\}^{d_1} \to \{0,1\}$ is a *$(t, k, \varepsilon_1)$-non-malleable extractor* if for every $(n, k)$-source $X$, uniform $Y$ on $\{0,1\}^{d_1}$ and functions $f_1, \dots, f_t : \{0,1\}^{d_1} \to \{0,1\}^{d_1}$ without fixed points, $(\mathrm{nmExt}(X, Y), \mathrm{nmExt}(X, f_1(Y)), \dots, \mathrm{nmExt}(X, f_t(Y)), Y)$ is $\varepsilon_1$-close to the same tuple with its first entry replaced by a uniform bit.

Let $\mathrm{nmExt}$ be such an extractor and let $\mathrm{Ext} : \{0,1\}^n \times \{0,1\}^{d_2} \to \{0,1\}^{d_1}$ be a seeded extractor for min-entropy $k/2$ with error $\varepsilon_2$ such that $\mathrm{Ext}(y, s) \ne \mathrm{Ext}(y, s')$ whenever $s \ne s'$. With $\{0,1\}^{d_2} = \{s_1, \dots, s_{D_2}\}$, define

$$
\mathrm{reduce}(x, y) = \mathrm{nmExt}(x, \mathrm{Ext}(y, s_1)) \circ \dots \circ \mathrm{nmExt}(x, \mathrm{Ext}(y, s_{D_2})).
$$

If $X$ and $Y$ are independent $(n, k)$-sources, then with probability at least $1 - n^{-\omega(1)}$ over $y \sim Y$, $\mathrm{reduce}(X, y)$ is a $(q, t, \gamma)$-non-oblivious bit-fixing source with $q = (\sqrt{\varepsilon_1} + \varepsilon_2)D_2$ and $\gamma = 5t\sqrt{\varepsilon_1}$. Consequently, if $\mathrm{bitExt}$ extracts from $(q, t, \gamma)$-non-oblivious bit-fixing sources on $D_2$ bits with error $\varepsilon$ (for instance a $(t, \gamma)$-independent $(q, \varepsilon')$-resilient function, that is, one with influence $I_{Q,D} \le \varepsilon'$ for every coalition $|Q| \le q$ and every $(t, \gamma)$-wise independent $D$, whose bias under every $(t, \gamma)$-wise independent distribution is at most $\varepsilon''$, with $\varepsilon = \varepsilon' + \varepsilon''$), then $(x, y) \mapsto \mathrm{bitExt}(\mathrm{reduce}(x, y))$ is a two-source extractor, strong in $Y$, with error at most $\varepsilon + n^{-\omega(1)}$.

## Proof sketch

For a $k$-source $X$, all but a $\sqrt{\varepsilon_1}$ fraction of seeds $r$ are good: the outputs of $\mathrm{nmExt}(X, \cdot)$ on any $t$ distinct good seeds are $5t\sqrt{\varepsilon_1}$-close to uniform (otherwise tampering functions mapping each bad seed to its witnesses break non-malleability). Since $\mathrm{Ext}$ is an extractor for min-entropy $k/2$, for all but a $2^{-k/2}$ fraction of $y$ the samples $\mathrm{Ext}(y, s_i)$ miss the bad seeds except on a $\sqrt{\varepsilon_1} + \varepsilon_2$ fraction, and those coordinates form the coalition $Q$. For each such $y$, $\mathrm{bitExt}$ outputs a nearly uniform bit, and the remaining $y$ cost $n^{-\omega(1)}$.

## Depends on

- [Two-source extractors](two-source-extractors.md)
- [Seeded randomness extractors](seeded-randomness-extractors.md)
- [k-sources, (k, ε)-sources and flat sources](weak-random-sources.md)
- [Coalition influence and resilient functions](resilient-functions.md)

## Proof depends on

- [Resilient functions extract from non-oblivious bit-fixing sources](resilient-functions-extract-from-nobf-sources.md)

## Sources

- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019; numbering of the ECCC report TR15-119: Definitions 1.11 and 1.12 (non-oblivious bit-fixing sources), Lemma 2.11 (resilient functions extract from them), Definition 3.2 (non-malleable extractor), Lemmas 3.4 and 3.5 (the reduction), and the proof of Theorem 1 in Section 6 (composition $\mathrm{2Ext}(x, y) = \mathrm{bitExt}(\mathrm{reduce}(x, y))$).
