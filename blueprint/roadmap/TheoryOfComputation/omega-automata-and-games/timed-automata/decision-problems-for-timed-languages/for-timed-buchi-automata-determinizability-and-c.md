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
constants at most $K$, are $\Pi^1_1$-hard as well. In particular all these problems are undecidable. The source writes
infinite timed words through the delays between letters and works with the timed Büchi automata of Alur and Dill, whose
timed words are the ones linked above.

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)
- [Timed words and timed languages](../timed-words-and-timed-languages.md)
- [Deterministic timed automata](../deterministic-timed-automata.md)
- [None](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

- [Universality of timed automata is undecidable](../universality-of-timed-automata-is-undecidable.md)

## Expansion

The proof reduces the universality problem for timed Büchi automata, which is $\Pi^1_1$-hard. Let $A$ be the timed regular
language of finite timed words over $\{a\}$ in which some two occurrences of $a$ are exactly one time unit apart; its
complement is not timed regular. Given a timed $\omega$-regular language $L$ over $\Sigma$ and a new letter $c$, let
$\mathcal{L}$ be the union of $A . (\mathcal{R} \times \{c\}) . (\mathcal{R} \times \Sigma)^\omega$, the infinite timed words with
no $c$ or at least two $c$'s, and $(\mathcal{R} \times \Sigma)^\star . (\mathcal{R} \times \{c\}) . L$. If $L$ is universal,
$\mathcal{L}$ is universal and is accepted, as is its empty complement, by a deterministic timed Büchi automaton without clocks.
Otherwise the complement of $\mathcal{L}$ is $A^c . (\mathcal{R} \times \{c\}) . L^c$ with $L^c$ nonempty, which no timed Büchi
automaton accepts, because it would have to check $A^c$ on the prefix; since deterministic timed Büchi languages are closed
under complement, $\mathcal{L}$ is not deterministic either.

## Sources

- O. Finkel, "Undecidable problems about timed automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, pp. 187–199, Springer, 2006, doi:10.1007/11867340_14; Theorem 9 of the version arXiv:0712.1363v1 with its proof, and the paragraph after it on Problems A and B.
