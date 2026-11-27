# AM = BP·NP: Arthur–Merlin as randomized reducibility to 3SAT

Write $L\le_r\mathrm{3SAT}$ when $L$ is randomly reducible to 3SAT: there is a probabilistic polynomial-time machine $M$ with $\Pr[M(x)\in\mathrm{3SAT}\iff x\in L]\ge2/3$ for every $x$. Following Arora and Barak, let $\mathsf{BP}\cdot\mathsf{NP}=\{L : L\le_r\mathrm{3SAT}\}$. Then $\mathsf{AM}=\mathsf{BP}\cdot\mathsf{NP}$, where $\mathsf{AM}$ is the two-message public-coin Arthur–Merlin class ($\mathsf{AM}[2]$ in Arora and Barak's notation).

## Proof sketch

In an AM protocol, Arthur's random string followed by Merlin's existential message is exactly a BP quantifier over an NP predicate; Cook–Levin turns the NP predicate into a 3SAT instance computed from the random string, and conversely a randomized reduction to 3SAT followed by Merlin's satisfying assignment is an AM protocol.

Derived here (not stated in the cited source): this class coincides with $\mathsf{BP}\cdot\mathsf{NP}$ defined by the BP operator applied to $\mathsf{NP}$, by the same Cook–Levin step. Consequently, if $\overline{\mathrm{3SAT}}\le_r\mathrm{3SAT}$ then $\overline{\mathrm{3SAT}}\in\mathsf{AM}$, hence $\mathsf{coNP}\subseteq\mathsf{AM}$ (as $\mathsf{AM}$ is closed under Karp reductions), and by Boppana–Håstad–Zachos the polynomial hierarchy collapses to $\Sigma_2^p$.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../time-and-space-complexity-classes/am.md)
- [The 3SAT decision problem](../../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [The BP and parity operators on complexity classes](../../../counting-complexity/counting-and-the-polynomial-hierarchy/the-bp-and-parity-operators-on-complexity.md)
- [Boppana–Håstad–Zachos: coNP ⊆ AM collapses PH to the second level](../../../randomized-and-quantum-complexity/arthur-merlin-and-merlin-arthur-classes/arthur-merlin-protocols/conp-in-am-collapses-ph.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Definitions 7.19 and 7.20, Definition 8.7 (AM is defined as AM[2]), and Section 8.4.2, item 1 (AM[2] = BP · NP, stated there without proof; Exercise 8.5).
