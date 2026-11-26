# Direct-sum simulation of many parallel queries

If a static problem has a cell-probe structure with $S$ cells of $w$ bits and query time $t$, then for every $k \le S/t$, answering $k$ queries in parallel against the same input yields a protocol in which Alice sends $O\!\left(k t \log_2 \frac{S}{k t}\right)$ bits and Bob sends $k t w$ bits, in $t$ rounds.

## Proof sketch

In round $j$, Alice needs the contents of the $j$-th probed cell of each of her $k$ queries, a set of at most $k$ cells among $S$; she encodes this set in $\log_2 \binom{S}{k} = O\!\left(k \log_2 \frac{S}{k}\right)$ bits instead of $k \log_2 S$ bits, and Bob returns the $k$ contents. Over $t$ rounds this costs $O(kt\log_2\frac{S}{kt})$ bits for Alice.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](../../../ComputerScience/data-structures/cell-sampling-and-range-counting-lower-bounds/static-cell-probe-structure.md)
- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)

## Proof depends on

- [Static cell-probe structures yield asymmetric protocols](cell-probe-to-asymmetric-protocol.md)

## Sources

- Mihai Pătraşcu, Mikkel Thorup, "Time-Space Trade-Offs for Predecessor Search", STOC (2006), arXiv:cs/0603043.
- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
