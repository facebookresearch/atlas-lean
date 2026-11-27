# Blockwise-dense sets (blockwise min-entropy)

Let $X \subseteq [m]^n$ be nonempty, $F \subseteq [n]$ and $\tau > 0$. The set $X$ is *$\tau$-dense on $F$* if for every nonempty $I \subseteq F$ and every assignment $\alpha \in [m]^I$, at most a $\tau^{-|I|}$ fraction of the elements of $X$ restrict to $\alpha$ on $I$; when $F = \varnothing$ the condition is vacuous. Equivalently, the uniform distribution on $X$ has blockwise min-entropy at least $\log_2 \tau$ per coordinate on $F$: every marginal on a nonempty $I \subseteq F$ has min-entropy at least $|I| \log_2 \tau$. The *deficiency* of a nonempty set $Y \subseteq (\{0,1\}^m)^F$ of Bob's inputs is $m|F| - \log_2 |Y|$, the deficiency of the uniform distribution on $Y$ (zero when $Y$ is everything, and finite because $Y \ne \varnothing$).

## Depends on

- [k-sources, (k, ε)-sources and flat sources](../../pseudorandomness-and-one-way-functions/weak-sources-and-extractors/weak-random-sources.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017.
- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020 (Definition 2.2: min-entropy, deficiency and blockwise min-entropy).
