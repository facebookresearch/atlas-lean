# For timed Büchi automata, determinizability and complementability are Π¹₁-hard

Deciding whether a timed Büchi automaton is equivalent to a deterministic one, or whether the complement of its timed
language is accepted by a timed Büchi automaton, is $\Pi^1_1$-hard, so both problems lie beyond the arithmetical hierarchy.

Let $\mathcal{A}$ range over [timed Büchi automata](../timed-buchi-automata.md), with diagonal-free clock constraints and no
$\varepsilon$-transitions, and let $L_\omega(\mathcal{A})$ be the set of infinite [timed words](../timed-words-and-timed-languages.md)
it accepts. Each of the following problems is $\Pi^1_1$-hard:

1. given $\mathcal{A}$, is $L_\omega(\mathcal{A})$ accepted by some [deterministic](../deterministic-timed-automata.md) timed Büchi
   automaton?
2. given $\mathcal{A}$, is the complement of $L_\omega(\mathcal{A})$ in the set of infinite timed words accepted by some timed
   Büchi automaton?

The bounded-resource versions, which ask for a witness in $TBA(n, K)$, the timed Büchi automata with at most $n$ clocks and
constants at most $K$, are $\Pi^1_1$-hard as well. In particular all these problems are undecidable. Following the source (Section 2), an infinite timed word is a sequence
$t_1 a_1 t_2 a_2 \cdots$ of positive delays $t_i$ and letters $a_i$, with no condition that time diverges, and complements
are taken in the set $(\mathbb{R}_{>0} \times \Sigma)^\omega$ of all such words; the [linked page](../timed-words-and-timed-languages.md)
instead requires the time stamps to be unbounded, a convention the source does not use.

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)
- [Timed words and timed languages](../timed-words-and-timed-languages.md)
- [Deterministic timed automata](../deterministic-timed-automata.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of timed automata is undecidable](../universality-of-timed-automata-is-undecidable.md)
- [Deterministic timed Muller automata are closed under Boolean operations](../deterministic-timed-muller-automata-are-closed-under-boolean.md)
- [Timed Büchi and timed Muller automata accept the same timed languages](../timed-buchi-and-timed-muller-automata-are-equally-expressive.md)

## Expansion

The proof reduces the universality problem for timed Büchi automata, which is $\Pi^1_1$-hard. Let $A$ be the timed regular
language of finite timed words over $\{a\}$ in which some two occurrences of $a$ are exactly one time unit apart; its
complement is not timed regular. Given a timed $\omega$-regular language $L$ over $\Sigma$ and a new letter $c$, let
$\mathcal{L}$ be the union of $A . (\mathcal{R} \times \{c\}) . (\mathcal{R} \times \Sigma)^\omega$, the infinite timed words with
no $c$ or at least two $c$'s, and $(\mathcal{R} \times \Sigma)^\star . (\mathcal{R} \times \{c\}) . L$. If $L$ is universal,
$\mathcal{L}$ is universal and is accepted, as is its empty complement, by a deterministic timed Büchi automaton without clocks.
Otherwise the complement of $\mathcal{L}$ is $A^c . (\mathcal{R} \times \{c\}) . L^c$ with $L^c$ nonempty, which no timed Büchi
automaton accepts, because it would have to check $A^c$ on the prefix. Then $\mathcal{L}$ is not deterministic either: a deterministic timed
Büchi automaton is a deterministic timed Muller automaton, the languages of deterministic timed Muller automata are closed
under complement, and timed Muller automata accept only timed $\omega$-regular languages, so the complement of $\mathcal{L}$
would be timed $\omega$-regular (the source cites Alur and Dill for the closure of deterministic regular timed
$\omega$-languages under complement).

The linked prerequisites are stated for timed words with strictly increasing, unbounded time stamps, while the source's words have positive delays and need not diverge, so a good expansion adds pages for these results over the source's timed words. For universality, the convergent words are accepted by a timed Büchi automaton that guesses a position, resets a clock there and accepts while the clock stays below $1$; adding this automaton to a given one turns universality over divergent words into universality over all of the source's words, so $\Pi^1_1$-hardness transfers. The complement closure of deterministic timed Muller automata and the equal expressiveness of timed Büchi and timed Muller automata are proved by constructions on automata that do not use divergence, and carry over with the same constructions.

## Sources

- O. Finkel, "Undecidable problems about timed automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, pp. 187–199, Springer, 2006, doi:10.1007/11867340_14; Theorem 9 of the version arXiv:0712.1363v1 with its proof, and the paragraph after it on Problems A and B.
