# Probabilistic automaton emptiness is undecidable for a fixed automaton

Emptiness of probabilistic automata stays undecidable for a fixed set of transition matrices, when only the starting distribution, or only the
vector of output values, is part of the input, and for automata with only two input letters.

A [probabilistic automaton](../probabilistic-automata-and-cut-point-languages.md) with $d$ states is given by stochastic $d \times d$ transition matrices $M_1, \dots, M_k$, one per input letter, a starting distribution
$\pi \in [0, 1]^d$ and an acceptance vector $\eta$. For a cutpoint $\lambda$, *emptiness* asks whether some sequence $i_1, \dots, i_m$ satisfies

$$
\pi^{T} M_{i_1} M_{i_2} \cdots M_{i_m} \eta > \lambda .
$$

**Theorem.**

1. Emptiness is undecidable for automata with a single accepting state given by
   - $4$ positive doubly stochastic $7 \times 7$ matrices, with cutpoint $1/7$;
   - $6$ fixed positive doubly stochastic $7 \times 7$ matrices, with cutpoint $1/7$, the only input being the starting distribution $\pi \in [0, 1]^7$;
   - $2$ positive $18 \times 18$ matrices, with cutpoint $1/18$;
   - $2$ fixed positive $28 \times 28$ matrices, with cutpoint $1/28$.
2. For every cutpoint $0 < \lambda < 1$, emptiness with an output vector $\eta \in [0, 1]^d$ is undecidable for $4$ positive $6 \times 6$ matrices with a fixed deterministic start state, and for $5$ fixed positive
   $6 \times 6$ matrices with a fixed starting distribution, the only input being the output vector $\eta \in [0, 1]^6$.

All statements hold also with the weak inequality $\ge \lambda$. In the fixed cases a single probabilistic automaton, up to the starting distribution or the output values, has an undecidable emptiness problem.
This sharpens the classical undecidability of [emptiness for probabilistic automata](../emptiness-problem-for-probabilistic-automata.md).

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)
- [The Post correspondence problem is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proofs reduce a Post correspondence problem with few word pairs and one variable pair, obtained from a semi-Thue system with an undecidable individual word problem for a fixed target word: the
remaining pairs are fixed and only one word pair, which ends up in the starting distribution or the output vector, depends on the instance. The words are encoded over a binary alphabet and the
domino pairs by small matrices, so that the instance has a solution exactly when some product of matrices crosses a threshold; a gap amplification step then turns this into an emptiness question for a
probabilistic automaton with positive matrices.

## Sources

- G. Rote, "Probabilistic finite automaton emptiness is undecidable for a fixed automaton", in *50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025)*, LIPIcs 345, paper 86, 2025, doi:10.4230/LIPIcs.MFCS.2025.86; read in arXiv:2412.05198v1: the two main theorems of Section 1 on forward and backward PFA emptiness with their numbers of matrices and states, the formal problem definition, the theorem on Post correspondence instances with one variable pair, and the gap amplification theorem.
