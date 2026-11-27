# Full-range lemma for dense pointer sets

For every constant $c \ge 0$ there is $n_0$ such that the following holds for all $n \ge n_0$, all $m \ge n^{1.1}$ and all $N \le n$. Let $X \subseteq [m]^N$ have blockwise min-entropy at least $0.95 \log_2 m - c$ (that is, $X$ is $m^{0.95} 2^{-c}$-dense on $[N]$) and let $Y \subseteq (\{0,1\}^m)^N$ satisfy $|Y| > 2^{mN - n \log_2 m}$. Then there is **one** pointer vector $x^* \in X$ such that for every target $\beta \in \{0,1\}^N$ there is $y_\beta \in Y$ with $\mathrm{Ind}_m(x^*_i, (y_\beta)_i) = \beta_i$ for all $i \in [N]$. In other words, the lifted gadget takes every value on $[N]$ already on the row $\{x^*\} \times Y$.

The quantifiers matter: a single $x^*$ works for all targets. The hypotheses are on entropy relative to $\log_2 m$ and on the size of $Y$; a bare inequality between the density parameter, $N$ and the deficiency of $Y$ does not suffice for large $m$.

## Proof sketch

Suppose every $x \in X$ misses some target $\beta_x$. Each $x$ is a block-respecting set of $N$ positions in $[mN]$, and $y$ avoids $\beta_x$ on $x$ exactly when it satisfies a clause on those positions; by a monotonization argument the number of $y$ satisfying all these clauses is largest when every $\beta_x$ is the all-ones string. The blockwise robust sunflower lemma (Alweiss–Lovett–Wu–Zhang, in Rao's blockwise form) applies to $X$ because its blockwise min-entropy exceeds $\log_2(K \log_2(N/\kappa))$ for $\kappa = 2^{-n \log_2 m}$ once $n$ is large, and it shows that a uniformly random $y$ contains the all-ones pattern on some $x \in X$ except with probability $\kappa$. So at most $\kappa 2^{mN} = 2^{mN - n\log_2 m}$ strings $y$ avoid every $\beta_x$, contradicting the size of $Y$.

## Depends on

- [Blockwise-dense sets (blockwise min-entropy)](blockwise-dense-pointer-sets.md)
- [Index gadget and lifted search problems](index-gadget-and-lifted-search-problems.md)

## Sources

- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020 (Lemma 3.2, Full Range Lemma, stated with $0.95 \log m - O(1)$ and proved for $n$ large; Lemma 2.2, blockwise approximate sunflower lemma).
- S. Lovett, R. Meka, I. Mertz, T. Pitassi and J. Zhang, "Lifting with Sunflowers", ITCS 2022 (Lemma 5.1).
- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017.
