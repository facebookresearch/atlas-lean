# Unconditional frontier lower bounds of (2 - ε)n

Let $S_n\subseteq U^n$ ($|U|\ge2$) be $K_n$-rectangle-free with $\log K_n=o(n)$ and $n\log|U|-\log|S_n|=o(n)$. Then for every fan-in $r\ge2$, every $\varepsilon>0$ and all large $n$, every circuit of fan-in at most $r$ deciding $S_n$, over any basis on $U$, has $s$ multiary gates with $(r-1)s>(2-\varepsilon)n$; for fan-in two, $s>(2-\varepsilon)n$. The same coefficient holds in the average-case setting: if $S_n$ has bias at most $b_n$ on rectangles with sides at least $K_n$ ($\log K_n=o(n)$, $b_n\to0$ suitably), then circuits with at most $(2-\varepsilon)n$ multiary gates agree with $S_n$ on at most a $\tfrac12+o(1)$ fraction of inputs.

## Proof sketch

Instantiate the frontier lower bound with $A=1$, which holds unconditionally by spanning-tree layouts; the average-case version replaces the counting lemma by a bias-weighted version.

## Depends on

- [Rectangle-free sets and rectangle bias](rectangle-free-sets-and-rectangle-bias.md)

## Proof depends on

- [The frontier lower bound for circuits of bounded fan-in](the-frontier-lower-bound.md)
- [Spanning-tree layouts give the layout hypothesis with A = 1](spanning-tree-layouts.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
