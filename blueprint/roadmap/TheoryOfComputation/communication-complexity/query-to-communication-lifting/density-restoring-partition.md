# Density-restoring partition

For every nonempty $X \subseteq [m]^n$ and $\tau > 1$ there are a partition $X = X^1 \sqcup \dots \sqcup X^\ell$ into nonempty parts and sets $I_j \subseteq [n]$ such that each part $X^j$ is fixed on $I_j$ (all its elements agree on the coordinates of $I_j$) and is $\tau$-dense on $[n] \setminus I_j$, and, writing $X^{\ge j} = X^j \sqcup \dots \sqcup X^\ell$, each part is large in what remains: $|X^j| \ge \tau^{-|I_j|}|X^{\ge j}|$.

## Proof sketch

Given the remaining set $X^{\ge j}$, take an inclusion-maximal $I_j$, possibly empty, with an assignment $\alpha_j$ such that more than a $\tau^{-|I_j|}$ fraction of $X^{\ge j}$ restricts to $\alpha_j$ (or $I_j = \varnothing$, $X^j = X^{\ge j}$ if there is none), split off $X^j = \{x \in X^{\ge j} : x_{I_j} = \alpha_j\}$, and recurse. If $X^j$ violated density on some nonempty $I^* \subseteq [n] \setminus I_j$ with assignment $\alpha^*$, then $\alpha_j \alpha^*$ would occur in more than a $\tau^{-|I_j \cup I^*|}$ fraction of $X^{\ge j}$, contradicting maximality.

## Depends on

- [Blockwise-dense sets (blockwise min-entropy)](blockwise-dense-pointer-sets.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017.
- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020 (Algorithm 1, Phase I, and Claim 3.4; there the threshold is $\tau = m^{0.95}$ and the loop stops once half of $X$ is covered).
