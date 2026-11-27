# Yap: coNP ⊆ NP/poly collapses PH to Σ₃

If $\mathsf{coNP}\subseteq\mathsf{NP}/\mathrm{poly}$ (equivalently $\mathrm{UNSAT}\in\mathsf{NP}/\mathrm{poly}$), then $\Sigma_2^p\subseteq\mathsf{NP}/\mathrm{poly}$ and

$$
\mathsf{PH}=\Sigma_3^p=\Pi_3^p .
$$

## Proof sketch

Given $L\in\Pi_3^p$ of the form $\forall\exists\forall$, a $\Sigma_3^p$ machine guesses advice for the inner $\mathsf{coNP}$ (hence $\mathsf{NP}/\mathrm{poly}$) predicate, universally checks that the advice is correct on all instances of the relevant length (soundness is a $\mathsf{coNP}$ condition and completeness a $\Pi_2^p$ condition, so the whole test stays within $\Sigma_3^p$), and then evaluates; this gives $\Pi_3^p\subseteq\Sigma_3^p$.

## Depends on

- [NP/poly](np-with-polynomial-advice.md)
- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)

## Proof depends on

- [UNSAT is coNP-complete](../../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)
- [Collapse of the polynomial hierarchy to a level](../../polynomial-hierarchy/collapse-of-the-polynomial-hierarchy-to-a-level.md)
- [Karp-Lipton theorem: NP in P/poly collapses PH](../../karp-lipton.md)

## Sources

- Chee K. Yap, "Some Consequences of Non-Uniform Conditions on Uniform Classes", Theoretical Computer Science 26(3), 1983.
