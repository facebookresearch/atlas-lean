# Bisimilarity of visibly pushdown register automata is undecidable

No algorithm decides whether two configurations of a visibly pushdown register automaton are bisimilar, already under the most restrictive register discipline, in contrast to automata without a stack, where bisimilarity is decidable.

**Theorem.** Bisimilarity for [visibly pushdown register automata](visibly-pushdown-register-automata.md) under the SF register discipline is undecidable: no algorithm decides, given an $r$-VPDRA(SF) and two of its configurations, whether they are bisimilar. The reduction produces automata with $r=2$ registers. An instance is the automaton's finite tables and two configurations, whose stacks and register contents are finite sequences of data values; since the transition system only compares data values for equality, these may be written as natural numbers. In the reduction the two configurations have empty stacks and the same register assignment.

Since SF is the most restrictive register discipline considered by the source, the undecidability extends to pushdown register automata under all the disciplines it studies.

## Depends on

- [Visibly pushdown register automata](visibly-pushdown-register-automata.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from emptiness of one-way universal register automata with two registers, undecidable by Demri and Lazić. From such an automaton $U$ one builds a 2-VPDRA $\mathcal A_U$ with configurations $\kappa_1,\kappa_2$ such that $U$ accepts some word iff $\kappa_1$ and $\kappa_2$ are not bisimilar. In the bisimulation game, Attacker first pushes a data word of his choice on the stack while Defender copies; then the two nearly identical components simulate $U$, the top of the stack playing the input head and the two registers those of $U$. Attacker guesses the outcomes of comparisons, and Defender can check a guess through Defender Forcing gadgets; universal branching is delegated to Defender in the same way; a wrong guess when loading a register leads to a deadlock. Rejecting states are made bisimilar and accepting states non-bisimilar.

## Sources

- Andrzej S. Murawski, Steven J. Ramsay and Nikos Tzevelekos, "Bisimilarity in fresh-register automata", *Logical Methods in Computer Science* 21(1), 2025, paper 13, doi:[10.46298/lmcs-21(1:13)2025](https://doi.org/10.46298/lmcs-21(1:13)2025); read in arXiv:2005.06411v5 ([arXiv](https://arxiv.org/abs/2005.06411v5)), whose numbering is used: Theorem 8.3 and its proof and Definition 8.2 (one-way universal register automata), in Section 8 (Visibly pushdown automata with single assignment and filled registers).
