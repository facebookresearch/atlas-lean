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

- Adding a dummy quantifier block preserves membership in a level (proof prerequisite for item 3; not yet stated)

## Sources

- Markus Krötzsch, Stephan Mennicke and Lukas Gerlach, *Complexity Theory*, Lecture 17: The Polynomial Hierarchy, TU Dresden, lecture slides of 11 December 2023, <https://iccl.inf.tu-dresden.de/w/images/e/e5/CT2023-Lecture-17-print.pdf>: Theorem 17.5 ($\Sigma_1^p = \mathsf{NP}$, $\Pi_1^p = \mathsf{coNP}$), Theorem 17.6 ($\mathrm{co}\Sigma_i^p = \Pi_i^p$), Theorem 17.7 ($\Sigma_i^p \subseteq \Pi_{i+1}^p$) and Theorem 17.9 (the certificate characterization with certificates of length at most $p(|w|)$, the convention of the pages above). The slides define the levels by alternating Turing machines; Theorem 17.9 is what identifies them with the certificate classes used here.
- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Definition 5.4 and Remark 5.5, with certificates of length exactly $q(|x|)$. Remark 5.5 prints the second equality as $\Pi_2^p = \mathsf{coNP}$; the intended and correct index is $\Pi_1^p$.
