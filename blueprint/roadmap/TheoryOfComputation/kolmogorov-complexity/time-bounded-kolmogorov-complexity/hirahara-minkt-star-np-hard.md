# Hirahara: MINKT* is NP-hard under randomized reductions

Every language in NP reduces to MINKT\* by a polynomial-time randomized many-one reduction with one-sided error: yes-instances always map to yes-instances, and no-instances map to no-instances with probability at least $2/3$. Consequently if $\mathrm{MINKT}^* \in \mathrm{BPP}$ then $\mathrm{NP} \subseteq \mathrm{BPP}$, and if $\mathrm{MINKT}^* \in \mathrm{coRP}$ then $\mathrm{NP} \subseteq \mathrm{coRP}$.

## Proof sketch

Reduce from $\mathrm{GapCMMSA}_{g,\varepsilon}$ with small soundness $\varepsilon$ (Hirahara, Theorem 5.2): assign each weighted variable a random seeded function, lay out a partial truth table whose defined entries force any consistent string to encode the selected variables of a satisfying assignment, and set the size threshold to the weight bound. Yes-instances have consistent strings produced quickly by a short generator; for no-instances, a counting argument over strings of small time-bounded complexity shows that with high probability over the seeds none is consistent.

## Depends on

- [Partial-string time-bounded Kolmogorov problem MINKT*](the-minkt-star-problem.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class RP](../../complexity-classes/time-and-space-complexity-classes/rp.md)

## Proof depends on

- [Collective Minimum Monotone Satisfying Assignment (CMMSA)](../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/collective-minimum-monotone-satisfying-assignment.md)
- [Min-Rep reduction: Label Cover to CMMSA, and NP-hardness of GapCMMSA](../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/label-cover-to-cmmsa-reduction.md)
- [Few strings have small time-bounded complexity](few-strings-have-small-time-bounded-complexity.md)

## Sources

- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022; ECCC TR22-119, Definition 5.1 and Theorem 5.2.
