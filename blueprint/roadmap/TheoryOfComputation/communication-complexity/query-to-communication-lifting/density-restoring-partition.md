# Density-restoring partition

For every $X \subseteq [m]^n$ and $\tau > 1$ there is a partition $X = X^1 \cup \dots \cup X^\ell$ and sets $I_j \subseteq [n]$ such that each part $X^j$ is fixed on $I_j$ (all its elements agree on the coordinates of $I_j$) and is $\tau$-dense on $[n] \setminus I_j$, and the parts are ordered so that $|X^{\ge j}|$ shrinks by at most a factor $\tau^{|I_j|}$ relative to $X$ when $X^j$ is removed: $|X^j| \ge \tau^{-|I_j|}|X^{\ge j}|$.

## Proof sketch

Repeatedly take a maximal set $I$ of coordinates and an assignment $\alpha$ violating density for the remaining set (the most heavily shared one), split off the elements restricting to $\alpha$ on $I$, and recurse; maximality of $I$ makes the split-off part dense on the complement.

## Depends on

- [Blockwise-dense sets (blockwise min-entropy)](blockwise-dense-pointer-sets.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017.
- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020.
