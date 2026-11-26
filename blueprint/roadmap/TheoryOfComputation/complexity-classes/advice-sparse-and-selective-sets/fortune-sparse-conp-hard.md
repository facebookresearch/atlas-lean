# Fortune: a sparse coNP-hard set implies P = NP

If some sparse language is $\mathsf{coNP}$-hard under polynomial-time many-one reductions, then $\mathsf{P}=\mathsf{NP}$. More generally, if $\mathrm{SAT}$ (equivalently $\mathrm{UNSAT}$) reduces to a set $S$ that is contained in a polynomial-time decidable set $G$ with $G\setminus S$ sparse, then $\mathrm{SAT}\in\mathsf{P}$.

## Proof sketch

Run the self-reduction tree of a formula level by level. Map each node (a partial assignment) by the reduction of UNSAT to the sparse set: nodes mapping to the same string are equisatisfiable, so keep one node per image; images known to be in the sparse set's 'unsatisfiable' part are pruned. Sparseness keeps every level polynomial in size while always retaining a satisfiable node if one exists.

## Depends on

- [Sparse decision problems](../mahaney-s-theorem/sparse.md)
- [The class coNP](../the-classes-p-np-and-conp/co-np.md)
- [The complexity class P](../the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [UNSAT is coNP-complete](../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)
- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Steven Fortune, "A Note on Sparse Complete Sets", SIAM Journal on Computing 8(3), 1979.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Exercise 3.12.
