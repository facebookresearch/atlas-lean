# MOCSP is NP-hard under randomized reductions

Circuit minimization relative to an oracle truth table given in the input, MOCSP, is NP-hard under randomized many-one reductions with one-sided error and under zero-error randomized Turing reductions. Improving this to deterministic truth-table reductions would separate EXP from ZPP.

**Theorem (Ilango).**

1. $\mathrm{NP}\le^{\mathrm{RP}}_m\mathrm{MOCSP}$: there is a randomized polynomial-time many-one reduction from an NP-complete problem to MOCSP that maps yes-instances to yes-instances always and errs only by producing a yes-instance from a no-instance.
2. $\mathrm{NP}\le^{\mathrm{ZPP}}_T\mathrm{MOCSP}$: NP is decided with zero error by a probabilistic polynomial-time oracle machine with an MOCSP oracle that may output "don't know" with probability at most $1/2$.
3. If NP reduces to MOCSP under polynomial-time truth-table reductions, then $\mathrm{EXP}\ne\mathrm{ZPP}$.

## Expansion

The reduction is from approximating Set Cover within a factor of $6$: given sets $S_1,\dots,S_t\subseteq[n]$ covering $[n]$ and a number $c$, it builds a random truth table $T$ and oracle table $O$ whose oracle circuit size tracks the optimal cover size $\ell$. A cover of size $\ell$ gives an $O$-oracle circuit for $T$ whose size bound does not depend on the random choices, which makes the error one-sided. Purported yes answers can be checked using the search-to-decision reduction for Set Cover, which turns the RP reduction into a ZPP Turing reduction. Item 3 adapts the arguments of Murray–Williams and Hitchcock–Pavan for MCSP.

Known unstated proof prerequisites needed before this node is ready for formalization:

- Nondeterministic time hierarchy for polynomial versus exponential time bounds ($\mathrm{NEXP} \not\subseteq \mathrm{NP}$, Žák, used in Ilango Appendix B, Theorem B.2)
- Murray–Williams substring lemma ($\mathrm{CC}(f_S) \le \mathrm{CC}(f_T) + c \log |T|$ for every substring $S$ of $T$, *Theory of Computing* Lemma 2.3, used in Ilango Proposition B.1)

## Depends on

- [MOCSP: circuit minimization with an oracle truth table in the input](mocsp-circuit-minimization-with-an-input-oracle.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)

## Proof depends on

- [Lund–Yannakakis–Feige: Set Cover is NP-hard to approximate within every constant](../../../pcp-and-inapproximability/approximation-hardness-of-classical-problems/set-cover-hardness-of-approximation.md)
- [Nondeterministic time hierarchy](../../../hierarchy-theorems-and-barriers/nondet-time-hierarchy.md)
- [Adleman's theorem: BPP is contained in P/poly](../../../randomized-and-quantum-complexity/adleman.md)

## Sources

- Rahul Ilango, "Approaching MCSP from Above and Below: Hardness for a Conditional Variant and AC0[p]", *Innovations in Theoretical Computer Science Conference (ITCS)*, 2020, https://doi.org/10.4230/LIPIcs.ITCS.2020.34 (Theorems 1.1, 1.2 and 3.1, Corollaries 3.4 and 3.5).
