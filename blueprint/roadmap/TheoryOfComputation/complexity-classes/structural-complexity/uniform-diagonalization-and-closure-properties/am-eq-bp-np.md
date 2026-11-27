# AM = BP·NP: Arthur–Merlin as randomized reducibility to 3SAT

A language $L$ is randomly reducible to 3SAT ($L\le_r\mathrm{3SAT}$: a probabilistic polynomial-time map $f$ with $\Pr[f(x)\in\mathrm{3SAT}\iff x\in L]\ge2/3$) iff $L\in\mathsf{BP}\cdot\mathsf{NP}$, and $\mathsf{AM}=\mathsf{AM}[2]=\mathsf{BP}\cdot\mathsf{NP}$. Consequently, if $\overline{\mathrm{3SAT}}\le_r\mathrm{3SAT}$ then $\mathsf{coNP}\subseteq\mathsf{AM}$ and the polynomial hierarchy collapses to $\Sigma_2^p$.

## Proof sketch

In an AM protocol, Arthur's random string followed by Merlin's existential message is exactly a BP quantifier over an NP predicate; Cook–Levin turns the NP predicate into a 3SAT instance computed from the random string. The collapse is Boppana–Håstad–Zachos.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../time-and-space-complexity-classes/am.md)
- [The BP and parity operators on complexity classes](../../../counting-complexity/counting-and-the-polynomial-hierarchy/the-bp-and-parity-operators-on-complexity.md)
- [The 3SAT decision problem](../../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [Boppana–Håstad–Zachos: coNP ⊆ AM collapses PH to the second level](../../../randomized-and-quantum-complexity/arthur-merlin-and-merlin-arthur-classes/arthur-merlin-protocols/conp-in-am-collapses-ph.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Definition 7.20, Exercise 8.5.
