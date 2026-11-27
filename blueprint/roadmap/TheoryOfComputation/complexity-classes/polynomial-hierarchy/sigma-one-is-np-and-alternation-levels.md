# The first level of the polynomial hierarchy is NP, and each level lies in the next universal level

Let $\Sigma_i^p$ and $\Pi_i^p$ be the existing classes with alternating quantifier blocks over bitstrings of length at most a polynomial in the input length, starting with $\exists$ and $\forall$ respectively, and a polynomial-time Boolean predicate. Let $\mathsf{PH}$ be the union of the existential levels. Then:

1. $\Sigma_1^p = \mathsf{NP}$ and $\Pi_1^p = \mathsf{coNP}$;
2. $\Pi_i^p = \mathrm{co}\Sigma_i^p$ for every $i \ge 1$;
3. $\Sigma_i^p \subseteq \Pi_{i+1}^p$ for every $i \ge 1$, so the polynomial hierarchy is also $\bigcup_{i > 0} \Pi_i^p$.

## Depends on

- [The polynomial hierarchy](../time-and-space-complexity-classes/ph.md)

- [The class $\Sigma_k^p$](../time-and-space-complexity-classes/sigma-k.md)
- [The universal levels of the polynomial hierarchy](../time-and-space-complexity-classes/pi-k.md)
- [The complexity class NP](../the-classes-p-np-and-conp/np.md)
- [The class coNP](../the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [Alternating bounded quantifiers](../time-and-space-complexity-classes/alt-quant.md)
- [The class $\Sigma_k^p$](../time-and-space-complexity-classes/sigma-k.md)
- [The universal levels of the polynomial hierarchy](../time-and-space-complexity-classes/pi-k.md)
- [The complexity class NP](../the-classes-p-np-and-conp/np.md)
- [The class coNP](../the-classes-p-np-and-conp/co-np.md)

## Expansion

This page becomes ready once:

- Agreement of the source's exact-length quantifier blocks with the blocks over bitstrings of length at most $p(|x|)$ used by [the class $\Sigma_k^p$](../time-and-space-complexity-classes/sigma-k.md) (proof prerequisite for transferring the cited exact-length formulation; not yet stated)
- Adding a dummy quantifier block preserves membership in a level (proof prerequisite for item 3; not yet stated)

## Sources

- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Definition 5.4 and Remark 5.5.
