# Fortune: a sparse coNP-hard set implies P = NP

If some sparse language is $\mathsf{coNP}$-hard under polynomial-time many-one reductions, then $\mathsf{P}=\mathsf{NP}$. More generally, if $\mathrm{SAT}$ (equivalently $\mathrm{UNSAT}$) reduces to a set $S$ that is contained in a polynomial-time decidable set $G$ with $G\setminus S$ sparse, then $\mathrm{SAT}\in\mathsf{P}$.

## Proof sketch

Let $f$ reduce SAT to $S\subseteq G$ with $G\setminus S$ sparse, and explore the tree of partial assignments of a formula level by level, mapping each node (the residual formula) by $f$. Nodes whose images lie outside $G$ are unsatisfiable and are pruned; nodes with equal images are equisatisfiable, so one node per image is kept. Unsatisfiable nodes have images in the sparse set $G\setminus S$, of which there are at most $p(n)$ of the relevant lengths, so keeping any $p(n)+1$ nodes with distinct images in $G$ retains a satisfiable node whenever the level contains one; every level stays polynomial and a satisfying assignment is found at the leaves if one exists. A sparse coNP-hard set $S'$ fits this form with $G=\{0,1\}^*$ and $S=\overline{S'}$.

## Depends on

- [Sparse decision problems](../../mahaney-s-theorem/sparse.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [UNSAT is coNP-complete](../../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)
- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Steven Fortune, "A Note on Sparse Complete Sets", SIAM Journal on Computing 8(3), 1979.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 3.12.
