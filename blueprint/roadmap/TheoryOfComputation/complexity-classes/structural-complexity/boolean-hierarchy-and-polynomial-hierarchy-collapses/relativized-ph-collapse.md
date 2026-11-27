# Relative P = NP collapses the relativized polynomial hierarchy

For every oracle $O$: if $\mathsf{P}^{O}=\mathsf{NP}^{O}$, then $\mathsf{PH}^{O}=\mathsf{P}^{O}$, where $\mathsf{PH}^O=\bigcup_k\Sigma_k^{p,O}$ and $\Sigma_{k+1}^{p,O}=\mathsf{NP}^{\Sigma_k^{p,O}}$ is defined by polynomial-time oracle verifiers with $k+1$ alternating polynomial quantifier blocks.

## Proof sketch

Induction on $k$: an innermost block of one quantifier over an $O$-oracle predicate is an $\mathsf{NP}^O$ (or $\mathsf{coNP}^O$) question, hence in $\mathsf{P}^O$, which removes one alternation.

## Depends on

- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [NP relative to an oracle](../../time-and-space-complexity-classes/npwith-oracle.md)
- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)

## Proof depends on

- [If P = NP then the polynomial hierarchy collapses to P](../../polynomial-hierarchy/ph-collapses.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 5, Exercise 9.
