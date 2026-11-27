# Boppana–Håstad–Zachos: coNP ⊆ AM collapses PH to the second level

If $\mathsf{coNP}\subseteq\mathsf{AM}$, then $\Sigma_2^p=\Pi_2^p=\mathsf{AM}$ and $\mathsf{PH}=\Sigma_2^p$. Consequently, if graph isomorphism is $\mathsf{NP}$-complete, then $\mathsf{PH}=\Sigma_2^p$.

## Proof sketch

$\Sigma_2^p=\exists\cdot\mathsf{coNP}\subseteq\exists\cdot\mathsf{AM}\subseteq\mathsf{MAM}=\mathsf{AM}$ by the round collapse, and $\mathsf{AM}\subseteq\Pi_2^p$; hence $\Sigma_2^p\subseteq\Pi_2^p$. GI is in $\mathsf{coAM}$, so NP-completeness would give $\mathsf{coNP}\subseteq\mathsf{AM}$.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../../complexity-classes/time-and-space-complexity-classes/am.md)
- [The class coNP](../../../complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

- [Babai–Moran: AM[k] = AM for every constant k](am-round-collapse.md)
- [AM is contained in $\Pi_2^p$ (Babai)](../am-subset-pi2.md)
- [Graph non-isomorphism is in AM](../../graph-isomorphism-and-arthur-merlin-proofs/graph-noniso-in-am.md)

## Sources

- Ravi B. Boppana, Johan Håstad and Stathis Zachos, "Does co-NP Have Short Interactive Proofs?", Information Processing Letters 25(2), 127–132, 1987.
- László Babai and Shlomo Moran, "Arthur–Merlin Games: A Randomized Proof System, and a Hierarchy of Complexity Classes", Journal of Computer and System Sciences 36(2), 254–276, 1988, Proposition 2 (derived there from the Collapse Theorem).
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
