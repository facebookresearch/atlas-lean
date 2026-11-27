# Bipartite perfect matching separates monotone and general circuit size

The language of adjacency matrices of subgraphs of $K_{n,n}$ having a perfect matching is in $\mathsf{P}$, hence in $\mathsf{P}/\mathsf{poly}$, and all of its slices are monotone functions; yet its slices require monotone circuits of size $n^{\Omega(\log n)}$. Thus the monotone circuit complexity of monotone functions in $\mathsf{P}$ can be superpolynomially larger than their general circuit complexity.

## Proof sketch

Bipartite matching reduces to maximum flow, which is in $\mathsf{P}$; $\mathsf{P}\subseteq\mathsf{P}/\mathsf{poly}$; Razborov's theorem gives the monotone bound.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Proof depends on

- [Razborov: monotone circuits for bipartite perfect matching need size n^{Ω(log n)}](razborov-monotone-perfect-matching-lower-bound.md)
- [Max flow is in P (Edmonds-Karp)](../../polynomial-time-problems/maximum-flow/max-flow-in-p.md)
- [P is contained in P/poly](../../complexity-classes/time-and-space-complexity-classes/p-is-contained-in-p-poly.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on Monotone Complexity of the Logical Permanent", Mathematical Notes of the Academy of Sciences of the USSR 37(6), 1985.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
