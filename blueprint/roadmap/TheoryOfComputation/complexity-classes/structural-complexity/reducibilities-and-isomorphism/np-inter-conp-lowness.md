# NP ∩ coNP is exactly the class of oracles low for NP

For every language $A$: $\mathsf{NP}^{A}=\mathsf{NP}$ if and only if $A\in\mathsf{NP}\cap\mathsf{coNP}$; and for $A\in\mathsf{NP}\cap\mathsf{coNP}$ also $\mathsf{P}^{A}\subseteq\mathsf{NP}\cap\mathsf{coNP}$. Analogously, for $A\in\mathsf{UP}\cap\mathsf{coUP}$, $\mathsf{P}^{A}\subseteq\mathsf{UP}\cap\mathsf{coUP}$.

## Proof sketch

A nondeterministic machine can replace each oracle query by guessing the answer together with an $\mathsf{NP}$ certificate for it or for its negation. Conversely $A,\overline{A}\in\mathsf{P}^A\subseteq\mathsf{NP}^A=\mathsf{NP}$. For UP, the certificates for answers are unique, so the overall accepting path is unique.

## Depends on

- [NP relative to an oracle](../../time-and-space-complexity-classes/npwith-oracle.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)
- [Unambiguous and few-witness polynomial time: UP and FewP](up-and-fewp.md)

## Sources

- Uwe Schöning, "A Low and a High Hierarchy within NP", Journal of Computer and System Sciences 27(1), 1983.
- Uwe Schöning, "Probabilistic Complexity Classes and Lowness", Journal of Computer and System Sciences 39(1), 1989.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
