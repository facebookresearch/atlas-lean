# Regularity of real-time Büchi one-counter ω-languages is Π¹₂-complete

Whether the $\omega$-language of a real-time Büchi one-counter automaton is $\omega$-regular is $\Pi^1_2$-complete.

**Theorem.** The regularity problem for [real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md) over $\Omega$ is $\Pi^1_2$-complete: $\{z\in\mathbb N: L(\mathcal C_z)\text{ is }\omega\text{-regular}\}$ is $\Pi^1_2$-complete.

The same holds for context-free $\omega$-languages given by Büchi pushdown automata (Corollary 3.18 of the source).

## Depends on

- [Real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

None.

## Expansion

Membership: $L(\mathcal C_z)$ is regular iff it equals $L(\mathcal C_y)$ for some index $y$ of an automaton that never changes its counter (a recursive set of indices), a number quantifier in front of a $\Pi^1_2$ equivalence. An injective computable reduction $H$ maps a Turing machine to a real-time Büchi one-counter automaton whose $\omega$-language is an effective coding of the machine's language plus the complement of the set of codes: Turing machines are first simulated by Büchi two-counter automata, then by real-time eight-counter automata on words padded with blocks $E^{S^n}$, then by real-time one-counter automata on words padded with blocks $0^{K^n}$, $K$ the product of the first eight primes. Hardness transfers the corresponding $\Pi^1_2$-completeness results of Castro and Cucker for nondeterministic Turing machines on infinite words: they give an injective computable $\varphi$ sending each $z$ in the complement of a $\Sigma^1_2$-complete set $U_2$, a $\Pi^1_2$-complete set (Notation 2.10 of the source), to a Turing machine accepting $\Sigma^\omega$, and each $z\in U_2$ to a machine whose $\omega$-language has a complement accepted by no Turing machine. Through $H\circ\varphi$ the first case gives automata accepting $\Omega^\omega$, which is regular; in the second the complement of the automaton's language is still accepted by no Turing machine, so the language is not regular. Hence the complement of $U_2$ 1-reduces to regularity.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Theorem 3.17 and its proof; Corollary 3.18.
