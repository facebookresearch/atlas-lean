# Containment of discounted-sum automata with multiple discount factors is undecidable

Whether one discounted-sum automaton with integral discount factors is below a deterministic one on every word is undecidable, on nonempty finite words for both strict and non-strict comparison and on infinite words for non-strict comparison.

Consider [discounted-sum automata with multiple discount factors](discounted-sum-automata-with-multiple-discount.md).

**Theorem.**
1. On finite words, no algorithm decides, given an integral NMDA $\mathcal N$ and an integral DMDA $\mathcal D$, whether $\mathcal N(w)\le\mathcal D(w)$ for all nonempty finite words $w \in \Sigma^+$; nor whether $\mathcal N(w)<\mathcal D(w)$ for all nonempty finite words $w \in \Sigma^+$. The source's Theorem 1 says "all finite words" but is meant for $\Sigma^+$, as its reduction (Section 3.1) quantifies over $w \in \Sigma^+$: on the empty word a DMDA has value $0$ and an NMDA has value $0$ or $+\infty$, so strict containment over all finite words never holds.
2. On infinite words, no algorithm decides, given an integral NMDA $\mathcal N$ and an integral DMDA $\mathcal D$, whether $\mathcal N(w)\le\mathcal D(w)$ for all infinite words $w$.

Since non-strict containment reduces to equivalence (compare $\mathcal A$ with the union of $\mathcal A$ and $\mathcal B$), equivalence of integral NMDAs is undecidable on finite and on infinite words (Theorem 3 of the source). Strict containment on infinite words is left open. By contrast, comparing a $\lambda_A$-NDA with a $\lambda_D$-DDA, each automaton having a single discount factor, is decidable in PSPACE (Theorem 4 of the source), and containment and equivalence of integral NDAs with different discount factors are decidable (Corollary 1).

## Depends on

- [Discounted-sum automata with multiple discount factors](discounted-sum-automata-with-multiple-discount.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the $0$-halting problem of two-counter machines (does the machine halt with both counters $0$). Input words encode sequences of machine commands. A deterministic automaton $\mathcal A$ with two states has value $1-1/D$ on the prefix up to the first halt command, $D$ being the product of its discount factors. The nondeterministic $\mathcal B$ guesses a violation: its gadgets check commands, zero tests and counter values, using pairs of *primal* and *dual* weight-and-discount choices on increment and decrement letters so that an excess of increments over decrements, or the reverse, changes the accumulated value in a detectable direction. Its value exceeds that of $\mathcal A$ exactly on a word that correctly describes a halting run, and is smaller on any finite word with a halt command that does not. On infinite words without a halt command both values converge to $1$, which is why only the non-strict version transfers to infinite words.

## Sources

- Udi Boker and Guy Hefetz, "On the Comparison of Discounted-Sum Automata with Multiple Discount Factors", in *Foundations of Software Science and Computation Structures (FoSSaCS 2023)*, Lecture Notes in Computer Science 13992, Springer, 2023, pp. 371–391, doi:[10.1007/978-3-031-30829-1_18](https://doi.org/10.1007/978-3-031-30829-1_18); numbering of arXiv:2301.04086v2 ([arXiv](https://arxiv.org/abs/2301.04086v2)): Lemma 1, Section 3.1 (the reduction), Lemma 2, Theorem 1 (finite words), Theorem 2 (infinite words), Theorem 3 (equivalence), Theorem 4 and Corollary 1 (automata with a single discount factor each).
