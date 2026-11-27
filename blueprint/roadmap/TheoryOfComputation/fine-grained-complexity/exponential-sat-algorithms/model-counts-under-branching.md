# Model counts under covering and partitioning branching

If a branching rule covers models then $\varphi$ is satisfiable iff some child is, and $\#_X(\varphi) \le \sum_i \#_X(\varphi_i)$, where $\#_X$ counts models over $X$. If it partitions models then $\#_X(\varphi) = \sum_i \#_X(\varphi_i)$ exactly, so the model count equals the sum of the counts at the leaves of any finite tree of partitioning branchings. The covering split of a clause $\ell_1\vee\ell_2$ into the children $\varphi\wedge\ell_1$ and $\varphi\wedge\ell_2$ does not partition models when some model of $\varphi$ satisfies both literals, and then the inequality can be strict.

## Proof sketch

Unfold the definitions; summing indicator functions over disjoint (resp. covering) families of model sets gives equality (resp. inequality), and induction over the tree gives the leaf identity.

## Depends on

- [Covering and partitioning branching rules for SAT](covering-and-partitioning-branching-rules.md)
- [Model count of a CNF formula](../../../Logic/propositional-logic/model-count-preserving-cnf-transformations/model-count.md)

## Sources

- F. V. Fomin and D. Kratsch, Exact Exponential Algorithms, Springer, 2010.
