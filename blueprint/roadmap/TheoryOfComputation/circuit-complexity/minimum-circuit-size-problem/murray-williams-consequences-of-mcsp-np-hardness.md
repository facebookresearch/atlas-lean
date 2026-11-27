# Murray–Williams: NP-hardness of MCSP implies EXP ≠ NP ∩ P/poly and EXP ≠ ZPP

If MCSP (truth table and binary threshold) is NP-hard under polynomial-time many-one reductions, then $\mathrm{EXP} \ne \mathrm{NP} \cap \mathrm{P/poly}$ and $\mathrm{EXP} \ne \mathrm{ZPP}$. In fact, if MCSP is NP-hard and $\mathrm{EXP} \subseteq \mathrm{P/poly}$, then $\mathrm{EXP} = \mathrm{NEXP}$.

## Proof sketch

A polynomial-time reduction from a sparse NEXP-complete padded language to MCSP produces truth tables that are themselves computable in exponential time, hence, if $\mathrm{EXP} \subseteq \mathrm{P/poly}$, of small circuit complexity; a short circuit for the reduction's output lets an exponential-time algorithm search all small circuits instead of all witnesses, putting NEXP in EXP. Combined with the nondeterministic time hierarchy and Karp–Lipton-style collapses this yields the separations.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [ZPP](../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Nondeterministic time hierarchy](../../hierarchy-theorems-and-barriers/nondet-time-hierarchy.md)

## Sources

- C. D. Murray and R. R. Williams, "On the (Non) NP-Hardness of Computing Circuit Complexity", Theory of Computing 13, 2017.
