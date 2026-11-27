# Element distinctness needs formulas of size about n^2/log n

Let $\mathrm{ED}_n$, for $n=2m\lceil\log_2 m\rceil$ and $m\ge1$, read $m$ blocks of $2\lceil\log_2 m\rceil$ bits each and output $1$ iff the $m$ blocks are pairwise distinct. Every formula over the full binary basis $B_2$ computing $\mathrm{ED}_n$ has leaf size $\Omega(n^2/\log n)$.

## Proof sketch

Apply Nechiporuk's bound with the blocks as the variable sets. A subfunction on one block is determined by the $m-1$ values taken by the other blocks, and different sets of $m-1$ distinct values give different subfunctions, so each block has at least $\binom{m^2}{m-1}$ subfunctions, $\log_2$ of which is $\Omega(m\log m)=\Omega(n)$; summing over the $m=\Theta(n/\log n)$ blocks gives $\Omega(n^2/\log n)$.

Derived here with explicit constants: with blocks of $k=2t$ bits and $m\le 2^t$, every formula over a basis of fan-in at most two computing $\mathrm{ED}_{m,2t}$ has leaf size $L$ with $m(m-1)t\le 4L+m$. Each block has at least $2^{t(m-1)}$ subfunctions: assign to the other blocks values $(j,w_j)$ tagged by their positions; different choices of the $w_j$ give different sets of forbidden values for the remaining block. Nechiporuk's bound sums $m$ such terms.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Nechiporuk's formula lower bound](nechiporuk-formula-lower-bound.md)

## Sources

- E. I. Nechiporuk, "On a Boolean function", Soviet Mathematics Doklady 7(4), 999–1000, 1966.
- Sam Buss, Math 262A lecture notes, "Nechiporuk's Theorem", University of California, San Diego, October 22, 2013 (Definition 2 and Proposition 1).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
