# Blockwise-dense sets (blockwise min-entropy)

Let $X \subseteq [m]^n$ and $F \subseteq [n]$. The set $X$ is *$\tau$-dense on $F$* if for every nonempty $I \subseteq F$ and every assignment $\alpha \in [m]^I$, at most a $\tau^{-|I|}$ fraction of the elements of $X$ restrict to $\alpha$ on $I$. Equivalently, the uniform distribution on $X$ has blockwise min-entropy at least $\log_2 \tau$ per coordinate on $F$. The *deficiency* of Bob's set $Y \subseteq (\{0,1\}^m)^F$ is $m|F| - \log_2 |Y|$.

## Sources

- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017.
- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020.
