# Probabilistic automaton emptiness is undecidable for a fixed automaton

Emptiness of probabilistic automata stays undecidable for a fixed set of transition matrices, when only the starting distribution, or only the
vector of output values, is part of the input, and for automata with only two input letters.

A [probabilistic automaton](../probabilistic-automata-and-cut-point-languages.md) with $d$ states is given by stochastic $d \times d$ transition matrices $M_1, \dots, M_k$ with rational entries, one per input letter, a starting distribution
$\pi$ with rational entries and an acceptance vector $\eta$, a $0$-$1$ vector marking the accepting states unless output values are allowed, in which case $\eta$ has rational entries in $[0, 1]$; all numbers are given as fractions of integers. For a cutpoint $\lambda$, *emptiness* asks whether some sequence $i_1, \dots, i_m$ satisfies

$$
\pi^{T} M_{i_1} M_{i_2} \cdots M_{i_m} \eta > \lambda .
$$

**Theorem.**

1. Emptiness is undecidable for automata with a single accepting state given by
   - $4$ positive doubly stochastic $7 \times 7$ matrices, with cutpoint $1/7$;
   - $6$ fixed positive doubly stochastic $7 \times 7$ matrices, with cutpoint $1/7$, the only input being the rational starting distribution $\pi$;
   - $2$ positive $18 \times 18$ matrices, with cutpoint $1/18$;
   - $2$ fixed positive $28 \times 28$ matrices, with cutpoint $1/28$.
2. For every cutpoint $0 < \lambda < 1$, emptiness with a rational output vector $\eta \in [0, 1]^d$ is undecidable for $4$ positive $6 \times 6$ matrices with a fixed deterministic start state, and for $5$ fixed positive
   $6 \times 6$ matrices with a fixed starting distribution, the only input being the rational output vector $\eta \in [0, 1]^6$.

All statements hold also with the weak inequality $\ge \lambda$. In the fixed cases a single probabilistic automaton, up to the starting distribution or the output values, has an undecidable emptiness problem.
This sharpens the classical undecidability of [emptiness for probabilistic automata](../emptiness-problem-for-probabilistic-automata.md).

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proofs reduce a Post correspondence problem with few word pairs and one variable pair, obtained from a semi-Thue system with an undecidable individual word problem for a fixed target word: the
remaining pairs are fixed and only one word pair, which ends up in the starting distribution or the output vector, depends on the instance. The words are encoded over a binary alphabet and the
domino pairs by small matrices, so that the instance has a solution exactly when some product of matrices crosses a threshold. After the column and row sums are made $1$, each matrix $C_i$ is mixed with the matrix $J$ whose entries are all $1/d$, $D_i = (1 - \alpha) J + \alpha C_i$ with $\alpha = 0.01$, which makes the matrices positive and stochastic (Section 2.6 of the source). The fixed-matrix cases use Post correspondence instances in which only one word pair varies, obtained from semi-Thue systems with an undecidable individual word problem (Matiyasevich and Sénizergues; Section 2.10 and Theorem 8 of the source). A good expansion adds and links pages for the undecidability of the individual word problem of a fixed semi-Thue system and for these Post correspondence instances with one variable pair.

## Sources

- G. Rote, "Probabilistic finite automaton emptiness is undecidable for a fixed automaton", in *50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025)*, LIPIcs 345, paper 86, 2025, doi:10.4230/LIPIcs.MFCS.2025.86; read in arXiv:2412.05198v1: Theorems 1 and 2 in Section 1.2 (forward and backward PFA emptiness with their numbers of matrices and states), the formal problem definition in Section 1.1, Section 2.10 and Theorem 8 in Appendix B (Post correspondence instances with one variable pair, from a semi-Thue system), Section 2.6 (positive matrices by mixing with the uniform matrix), and Theorem 7 (gap amplification, Gimbert and Oualhadj, in the outlook of Section 5.1), with the numbering of that version.
