# Hirahara: Partial MCSP is NP-hard under randomized reductions

Every NP language reduces to Partial MCSP (size threshold in unary or binary) by a polynomial-time randomized many-one reduction with one-sided error: yes-instances always map to yes-instances, and no-instances map to no-instances with probability at least $2/3$. Consequently $\mathrm{MCSP}^* \in \mathrm{BPP}$ implies $\mathrm{NP} \subseteq \mathrm{BPP}$, and $\mathrm{MCSP}^* \in \mathrm{coRP}$ implies $\mathrm{NP} \subseteq \mathrm{coRP}$.

## Proof sketch

Reduce from $\mathrm{GapCMMSA}$: give each weighted variable a random seeded Boolean function whose input length matches its weight, and build a partial truth table indexed by (formula, slot, mask, seeds) whose defined entries require a circuit to encode, for every formula, a satisfied term. Satisfying assignments of small weight give small circuits (completeness); conversely a small circuit determines a knowledge set of variables, and a counting argument over small circuits shows that with high probability no small circuit is consistent when every satisfying assignment is heavy.

## Depends on

- [Partial MCSP (MCSP*)](partial-minimum-circuit-size-problem.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class RP](../../complexity-classes/time-and-space-complexity-classes/rp.md)

## Proof depends on

- [Min-Rep reduction: Label Cover to CMMSA, and NP-hardness of GapCMMSA](../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/label-cover-to-cmmsa-reduction.md)

## Sources

- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022.
- D. Uhlig, "Networks Computing Boolean Functions for Multiple Input Values", in Boolean Function Complexity, Cambridge University Press, 1992.
