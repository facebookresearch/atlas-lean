# 3SAT reducing to its complement collapses PH to NP

If $\mathrm{3SAT}\le^{p}_{m}\overline{\mathrm{3SAT}}$, then $\mathsf{NP}=\mathsf{coNP}$ and hence $\mathsf{PH}=\mathsf{NP}$. Relatedly, $\mathsf{NP}=\mathsf{coNP}$ if and only if $\mathrm{3SAT}$ and $\mathrm{TAUTOLOGY}$ are polynomial-time many-one reducible to each other.

## Proof sketch

A reduction from an NP-complete set to its complement shows $\mathsf{NP}\subseteq\mathsf{coNP}$, and symmetrically $\mathsf{coNP}\subseteq\mathsf{NP}$; then every level $\Sigma_k^p$ collapses to $\mathsf{NP}$ by induction. TAUTOLOGY is coNP-complete, so mutual reducibility with 3SAT is exactly $\mathsf{NP}=\mathsf{coNP}$.

## Depends on

- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [TAUTOLOGY is coNP-complete](tautology-conp-complete.md)
- [Collapse of the polynomial hierarchy to a level](../../polynomial-hierarchy/collapse-of-the-polynomial-hierarchy-to-a-level.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 5, Exercise 3; Chapter 2, Exercise 7.
