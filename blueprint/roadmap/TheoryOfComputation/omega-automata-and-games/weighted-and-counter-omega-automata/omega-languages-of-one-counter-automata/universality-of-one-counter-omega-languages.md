# Universality of real-time Büchi one-counter automata is Π¹₂-complete

Whether a real-time Büchi one-counter automaton accepts every infinite word over its alphabet is $\Pi^1_2$-complete, at the second level of the analytical hierarchy, far beyond the arithmetical hierarchy.

**Theorem.** The universality problem for [real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md) over the alphabet $\Omega$ is $\Pi^1_2$-complete: the set $\{z\in\mathbb N: L(\mathcal C_z)=\Omega^\omega\}$ is $\Pi^1_2$-complete.

The same holds for the cofiniteness problem ($\Omega^\omega\setminus L(\mathcal C_z)$ finite; Theorem 3.13 of the source), and both problems are $\Pi^1_2$-complete for context-free $\omega$-languages given by Büchi pushdown automata (Corollaries 3.12 and 3.14). In particular they are not arithmetical, hence highly undecidable.

## Depends on

- [Real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Membership: $L(\mathcal C_z)=\Omega^\omega$ iff for every $\sigma\in\Omega^\omega$ there is $r\in\{0,1\}^\omega$ coding an accepting run on $\sigma$, two function quantifiers in front of an arithmetical matrix. Hardness transfers the corresponding $\Pi^1_2$-completeness results of Castro and Cucker for nondeterministic Turing machines on infinite words. An injective computable reduction $H$ maps a Turing machine to a real-time Büchi one-counter automaton whose $\omega$-language is an effective coding of the machine's language plus the complement of the set of codes: Turing machines are first simulated by Büchi two-counter automata, then by real-time eight-counter automata on words padded with blocks $E^{S^n}$, then by real-time one-counter automata on words padded with blocks $0^{K^n}$, $K$ the product of the first eight primes. Under $H$, a Turing machine accepts every infinite word iff the image automaton does.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Theorem 3.9 and its proof (Lemmas 3.6–3.8 for the reductions), Corollary 3.12, Theorem 3.13 and Corollary 3.14.
