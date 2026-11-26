# Selman: an NP-hard P-selective set implies P = NP

If some $\mathsf{NP}$-hard set (under polynomial-time many-one reductions) is P-selective, then $\mathsf{P}=\mathsf{NP}$. Equivalently, an $\mathsf{NP}$-complete set is P-selective iff $\mathsf{P}=\mathsf{NP}$.

## Proof sketch

P-selectivity is inherited by many-one preimages, so SAT would be P-selective. Then the self-reduction of SAT becomes a deterministic walk: at each variable, use the selector to choose between the formulas with the variable set to $0$ and to $1$, and finally check the resulting assignment.

## Depends on

- [P-selective sets](p-selective-sets.md)
- [NP-complete decision problems](../../mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Alan L. Selman, "P-Selective Sets, Tally Languages, and the Behavior of Polynomial Time Reducibilities on NP", Mathematical Systems Theory 13(1), 1979.
- Lane A. Hemaspaandra and Leen Torenvliet, "Theory of Semi-Feasible Algorithms", Springer, 2003.
