# If NP ⊆ BPP then PH = Σ₂, and P = NP implies P = BPP

(i) If $\mathsf{NP}\subseteq\mathsf{BPP}$, then $\mathsf{NP}\subseteq\mathsf{P}/\mathrm{poly}$ and hence $\mathsf{PH}=\Sigma_2^p$; moreover $\mathsf{NP}=\mathsf{RP}$. (ii) If $\mathsf{P}=\mathsf{NP}$, then $\mathsf{BPP}=\mathsf{P}$.

## Proof sketch

(i) Adleman's theorem gives $\mathsf{BPP}\subseteq\mathsf{P}/\mathrm{poly}$, then Karp–Lipton; for $\mathsf{NP}=\mathsf{RP}$ use the BPP algorithm for SAT within the self-reduction and verify the final assignment. (ii) Sipser–Gács–Lautemann puts BPP in $\Sigma_2^p$, which collapses to $\mathsf{P}$ when $\mathsf{P}=\mathsf{NP}$.

## Depends on

- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)

## Proof depends on

- [Adleman's theorem: BPP is contained in P/poly](../../adleman.md)
- [Karp-Lipton theorem: NP in P/poly collapses PH](../../../complexity-classes/karp-lipton.md)
- [Sipser-Gács-Lautemann: BPP is in $\Sigma_2^p$ and $\Pi_2^p$](../../sipser-gacs-lautemann.md)
- [If P = NP then the polynomial hierarchy collapses to P](../../../complexity-classes/polynomial-hierarchy/ph-collapses.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Ker-I Ko, "Some Observations on the Probabilistic Algorithms and NP-hard Problems", Information Processing Letters 14(1), 39–43, 1982 ($\mathsf{NP}\subseteq\mathsf{BPP}$ implies $\mathsf{NP}=\mathsf{RP}$).
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
