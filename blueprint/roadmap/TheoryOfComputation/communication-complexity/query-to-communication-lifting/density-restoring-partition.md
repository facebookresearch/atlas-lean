# Density-restoring partition

Let $m\ge2$ and let $X \subseteq [m]^n$ be nonempty (blocks indexed by $J=[n]$). Write $\tau=m^{0.9}$, so that $X$ is $\tau$-dense on a set of blocks exactly when the uniform distribution on $X$ has min-entropy rate at least $0.9$ on every nonempty subset of those blocks. There are a partition $X = X^1 \sqcup \dots \sqcup X^\ell$ into nonempty parts and sets $I_j \subseteq J$ such that each part $X^j$ is fixed on $I_j$ (all its elements agree on the blocks of $I_j$) and is $\tau$-dense on $J \setminus I_j$, and, writing $X^{\ge j} = X^j \sqcup \dots \sqcup X^\ell$, each part is large in what remains: $|X^j| \ge \tau^{-|I_j|}|X^{\ge j}|$. If $X$ is already $\tau$-dense on $J$, the partition has the single part $X$.

## Proof sketch

While the remaining set $X^{\ge j}$ is nonempty, take a maximal $I_j \subseteq J$, possibly empty, with an assignment $\alpha_j$ such that more than a $\tau^{-|I_j|}$ fraction of $X^{\ge j}$ restricts to $\alpha_j$ (if there is none, $I_j = \varnothing$ and $X^j = X^{\ge j}$), split off $X^j = \{x \in X^{\ge j} : x_{I_j} = \alpha_j\}$, and recurse. If $X^j$ violated density on some nonempty $K \subseteq J \setminus I_j$ with assignment $\beta$, then $\alpha_j \beta$ would occur in more than a $\tau^{-|I_j \cup K|}$ fraction of $X^{\ge j}$, contradicting maximality. Derived here: the same procedure and argument work verbatim for every threshold $\tau > 1$ in place of $m^{0.9}$.

## Depends on

- [Blockwise-dense sets (blockwise min-entropy)](blockwise-dense-pointer-sets.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017 (Definition 1 and the density-restoring partition with Lemma 5, Section 3.3 of arXiv:1703.07666v1).
- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020 (Algorithm 1, Phase I, and Claim 3.4; there the threshold is $\tau = m^{0.95}$ and the loop stops once half of $X$ is covered).
