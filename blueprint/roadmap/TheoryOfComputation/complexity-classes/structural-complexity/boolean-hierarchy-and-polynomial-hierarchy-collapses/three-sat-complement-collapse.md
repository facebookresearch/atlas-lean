# NP-complete sets have complements outside NP unless NP = coNP, which collapses PH to NP

If $\mathsf{NP}\ne\mathsf{coNP}$ and $S\in\mathsf{NP}$ is a set to which every set in $\mathsf{NP}$ is Karp-reducible, that is, polynomial-time many-one reducible (for instance $S=\mathrm{3SAT}$), then the complement $\{0,1\}^*\setminus S$ is not in $\mathsf{NP}$. Moreover, if $\mathsf{NP}=\mathsf{coNP}$ then $\mathsf{PH}=\mathsf{NP}$: the polynomial hierarchy collapses to its first level.

## Proof sketch

If every set in $\mathsf{NP}$ Karp-reduces to $S$, every set in $\mathsf{coNP}$ Karp-reduces to the complement of $S$, and $\mathsf{NP}$ is closed under Karp reductions, so a complement of $S$ in $\mathsf{NP}$ would give $\mathsf{coNP}\subseteq\mathsf{NP}$ and hence $\mathsf{NP}=\mathsf{coNP}$. The collapse is the case $i=1$ of the collapse of the hierarchy to a level.

Derived here (not stated in the main text of the cited sources; Arora–Barak pose them as exercises): if $\mathrm{3SAT}\le^{p}_{m}\overline{\mathrm{3SAT}}$, then $\overline{\mathrm{3SAT}}\in\mathsf{NP}$, so $\mathsf{NP}=\mathsf{coNP}$ and $\mathsf{PH}=\mathsf{NP}$; and since TAUTOLOGY is $\mathsf{coNP}$-complete, $\mathsf{NP}=\mathsf{coNP}$ if and only if $\mathrm{3SAT}$ and $\mathrm{TAUTOLOGY}$ are polynomial-time many-one reducible to each other.

## Depends on

- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [Polynomial-time many-one reduction](../../../np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [The 3SAT decision problem](../../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [TAUTOLOGY is coNP-complete](tautology-conp-complete.md)
- [Collapse of the polynomial hierarchy to a level](../../polynomial-hierarchy/collapse-of-the-polynomial-hierarchy-to-a-level.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Section 2.4.3, Proposition 2.34.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Section 5.2.1, Theorem 5.6, item 1 (the collapse), with Chapter 5, Exercise 3 and Chapter 2, Exercise 7.
