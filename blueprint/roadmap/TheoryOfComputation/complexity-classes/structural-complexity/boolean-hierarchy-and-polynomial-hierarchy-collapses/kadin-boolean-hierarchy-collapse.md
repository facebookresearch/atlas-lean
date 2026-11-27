# Kadin: a collapse of the Boolean hierarchy collapses PH to Σ₃

If the Boolean hierarchy collapses at some finite level, i.e. $\mathsf{coBH}_k\subseteq\mathsf{BH}_k$ (equivalently $\mathsf{BH}_{k+1}=\mathsf{BH}_k$) for some $k$, then $\mathsf{PH}$ collapses to $\mathsf{P}^{\mathsf{NP}^{\mathsf{NP}}[O(\log n)]}$, the languages decided in polynomial time with $O(\log n)$ queries to a $\Sigma_2^p$ oracle; in particular $\mathsf{PH}=\Sigma_3^p=\Pi_3^p$, and $\mathsf{DP}=\mathsf{coDP}$ already implies this collapse.

## Proof sketch

The 'hard/easy' argument: a reduction from $\mathsf{coBH}_k$ to $\mathsf{BH}_k$ yields, for each length, either an 'easy' situation decidable in NP or a 'hard' sequence of formulas usable as polynomial advice; encoding the hard sequences into a sparse oracle $T$ places $\mathsf{coNP}$ in $\mathsf{NP}^{T}\subseteq\mathsf{NP}/\mathrm{poly}$, and Yap's theorem gives $\mathsf{PH}=\Sigma_3^p$; a finer analysis of $T$ gives the $\mathsf{P}^{\mathsf{NP}^{\mathsf{NP}}[O(\log n)]}$ bound.

## Depends on

- [The difference class DP and the Boolean hierarchy over NP](dp-and-boolean-hierarchy.md)
- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)
- [The class $\Sigma_k^p$](../../time-and-space-complexity-classes/sigma-k.md)

## Proof depends on

- [Yap: coNP ⊆ NP/poly collapses PH to Σ₃](yap-conp-in-np-poly.md)

## Sources

- Jim Kadin, "The Polynomial Time Hierarchy Collapses if the Boolean Hierarchy Collapses", SIAM Journal on Computing 17(6), 1988.
- Richard Chang and Jim Kadin, "The Boolean Hierarchy and the Polynomial Hierarchy: A Closer Connection", SIAM Journal on Computing 25(2), 1996, Section 1 (statement of Kadin's collapse to $\mathsf{P}^{\mathsf{NP}^{\mathsf{NP}}[O(\log n)]}$).
