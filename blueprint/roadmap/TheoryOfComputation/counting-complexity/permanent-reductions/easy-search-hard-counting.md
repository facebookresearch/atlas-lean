# An easy search problem with a #P-complete counting problem

There is a relation $R\in\mathsf{PC}$ whose search problem is solvable in polynomial time (indeed every instance has an easily found solution) while counting its solutions is $\#\mathsf{P}$-complete under one-query (metric) reductions. For instance, adjoin to the perfect matchings of a bipartite graph one distinguished extra solution: search is trivial, and the count is $\#\mathrm{PM}+1$.

## Proof sketch

Subtracting one recovers the perfect-matching count, which is $\#\mathsf{P}$-complete by Valiant's theorem; the distinguished solution witnesses that search is easy.

## Depends on

- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [Search problems: FNP, FP and TFNP](../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Proof depends on

- [The permanent is #P-complete (Valiant)](../complexity-of-the-permanent/permanent-sharp-p-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 6.19.
