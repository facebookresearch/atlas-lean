# Element distinctness needs formulas of size about n^2/log n

Let $\mathrm{ED}_{m,k}$ read $m$ blocks of $k$ bits and output $1$ iff the blocks are pairwise distinct. With blocks of $k=2t$ bits and $m\le 2^t$, every formula over a basis of fan-in at most two computing $\mathrm{ED}_{m,2t}$ has leaf size $L$ with $m(m-1)t\le 4L+m$. Taking $t=\lceil\log_2 m\rceil$, the input length is $n=2m\lceil\log_2 m\rceil$ and $L=\Omega(n^2/\log n)$.

## Proof sketch

Each block has at least $2^{t(m-1)}$ subfunctions: assign to the other blocks values $(j,w_j)$ tagged by their positions; different choices of the $w_j$ give different sets of forbidden values for the remaining block. Nechiporuk's bound sums $m$ such terms.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Nechiporuk's formula lower bound](nechiporuk-formula-lower-bound.md)

## Sources

- E. I. Nechiporuk, "On a Boolean function", Soviet Mathematics Doklady 7(4), 999–1000, 1966.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
