# Kadin: a collapse of the Boolean hierarchy collapses PH to Σ₃

If the Boolean hierarchy collapses at some finite level, i.e. $\mathsf{coBH}_k\subseteq\mathsf{BH}_k$ (equivalently $\mathsf{BH}_{k+1}=\mathsf{BH}_k$) for some $k$, then $\mathsf{PH}=\Sigma_3^p=\Pi_3^p$. In particular $\mathsf{DP}=\mathsf{coDP}$ implies $\mathsf{PH}=\Sigma_3^p$.

## Proof sketch

The 'hard/easy' argument: a reduction from $\mathsf{coBH}_k$ to $\mathsf{BH}_k$ yields, for each length, either an 'easy' situation decidable in NP or a 'hard' sequence of formulas usable as polynomial advice; this places $\mathsf{coNP}$ in $\mathsf{NP}/\mathrm{poly}$, and Yap's theorem finishes.

## Depends on

- [The difference class DP and the Boolean hierarchy over NP](dp-and-boolean-hierarchy.md)
- [The polynomial hierarchy](../time-and-space-complexity-classes/ph.md)
- [The class $\Sigma_k^p$](../time-and-space-complexity-classes/sigma-k.md)

## Proof depends on

- [Yap: coNP ⊆ NP/poly collapses PH to Σ₃](yap-conp-in-np-poly.md)

## Sources

- Jim Kadin, "The Polynomial Time Hierarchy Collapses if the Boolean Hierarchy Collapses", SIAM Journal on Computing 17(6), 1988.
