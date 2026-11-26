# Static lower bound for two-dimensional range counting

Every static cell-probe structure for two-dimensional orthogonal range counting (dominance counting) on $n$ points in $[n]^2$ that uses $S$ cells of $w$ bits has query time $t = \Omega\!\left(\frac{\lg n}{\lg(S w / n)}\right)$. In particular, with $S = n (\lg n)^{O(1)}$ and $w = \Theta(\lg n)$, $t = \Omega(\lg n / \lg\lg n)$, which is matched by known structures.

## Proof sketch

Reduce lopsided set disjointness, through reachability oracles in butterfly graphs, to answering $k = \Theta(n/\lg n)$ parallel range counting queries on a point set encoding Bob's input. By the direct-sum simulation, a structure with query time $t$ gives Alice $O(k t \lg(Sw/n))$ bits and Bob $O(ktw)$ bits; the LSD tradeoff with $N = k$ and $B = n^{\Omega(1)}$ forces Alice to send $\Omega(k \lg n)$ bits, so $t \lg(Sw/n) = \Omega(\lg n)$.

## Depends on

- [Communication lower bound for lopsided set disjointness](lsd-tradeoff.md)
- [Direct-sum simulation of many parallel queries](direct-sum-simulation.md)

## Proof depends on

- [Communication lower bound for lopsided set disjointness](lsd-tradeoff.md)
- [Direct-sum simulation of many parallel queries](direct-sum-simulation.md)

## Sources

- Mihai Pătraşcu, "Lower Bounds for 2-Dimensional Range Counting", STOC (2007).
- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
