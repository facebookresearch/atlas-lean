# Static lower bound for two-dimensional range counting

Every static cell-probe structure for two-dimensional orthogonal range counting (dominance counting) on $n$ points in $[n]^2$ that uses $S$ cells of $w$ bits has query time $t = \Omega\!\left(\frac{\lg n}{\lg(S w / n)}\right)$. In particular, with $S = n (\lg n)^{O(1)}$ and $w = \Theta(\lg n)$, $t = \Omega(\lg n / \lg\lg n)$, which is matched by known structures.

## Proof sketch

Pătraşcu reduces lopsided set disjointness (in a doubly blocked form) on $N$ elements to $k = N/d$ parallel reachability queries in a subgraph of a butterfly graph of depth $d$, then reachability to two-dimensional rectangle stabbing, and stabbing to dominance range counting modulo $2$, with each rectangle replaced by its four corners. By the direct-sum simulation, a range-counting structure with space $S$ and query time $t$ gives a protocol in which Alice sends $O((N/d)\,t\lg(Sd/N))$ bits and Bob $O((N/d)\,t\,w)$ bits. Comparing with the LSD tradeoff and choosing the butterfly degree and depth appropriately forces $t = \Omega(\lg n/\lg(Sw/n))$.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](../../../ComputerScience/data-structures/cell-sampling-and-range-counting-lower-bounds/static-cell-probe-structure.md)

## Proof depends on

- [Communication lower bound for lopsided set disjointness](lsd-tradeoff.md)
- [Direct-sum simulation of many parallel queries](direct-sum-simulation.md)

## Sources

- Mihai Pătraşcu, "Lower Bounds for 2-Dimensional Range Counting", STOC (2007).
- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
