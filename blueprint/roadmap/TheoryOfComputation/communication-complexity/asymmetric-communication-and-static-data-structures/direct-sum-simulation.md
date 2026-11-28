# Direct-sum simulation of many parallel queries

If a static problem has a cell-probe structure with $S$ cells of $w$ bits and query time $t$, then for every $1 \le k \le S$, answering $k$ queries in parallel against the same input yields a protocol of $t$ exchanges ($2t$ messages) in which Alice sends $t \left\lceil \log_2 \binom{S}{k} \right\rceil$ bits and Bob sends $k t w$ bits, after which Alice knows all $k$ answers. For $k \le S/2$ this is $O\!\left(k t \log_2 \frac{S}{k}\right)$ bits for Alice, but not near $k = S$: at $k = S - 1$, $\log_2 \binom{S}{k} = \log_2 S$ while $k \log_2 \frac{S}{k} = O(1)$.

## Proof sketch

In round $j$, Alice needs the contents of the $j$-th probed cell of each of her $k$ queries, a set of at most $k$ cells among $S$; she pads it to exactly $k$ cells and sends its index among the $\binom{S}{k}$ such sets, $\left\lceil \log_2 \binom{S}{k} \right\rceil$ bits instead of $k \lceil \log_2 S \rceil$, and Bob returns the $k$ contents in a fixed order. Over $t$ exchanges this costs $t \left\lceil \log_2 \binom{S}{k} \right\rceil$ bits for Alice, after which she can finish every query.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](../../../ComputerScience/data-structures/cell-sampling-and-range-counting-lower-bounds/static-cell-probe-structure.md)
- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)

## Proof depends on

- [Static cell-probe structures yield asymmetric protocols](cell-probe-to-asymmetric-protocol.md)

## Sources

- Mihai Pătraşcu, Mikkel Thorup, "Time-Space Trade-Offs for Predecessor Search", STOC (2006), arXiv:cs/0603043.
- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
