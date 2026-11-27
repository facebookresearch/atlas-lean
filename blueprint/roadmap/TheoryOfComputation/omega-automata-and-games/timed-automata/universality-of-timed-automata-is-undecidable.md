# Universality of timed automata is undecidable

The *universality problem* asks, for a [timed Büchi automaton](timed-buchi-automata.md) $\mathcal{A}$ over an alphabet $\Sigma$,
whether $\mathcal{A}$ accepts every timed word over $\Sigma$. This problem is $\Pi^1_1$-hard, and in particular undecidable.

The proof encodes computations of a nondeterministic two-counter machine as timed words in which the $j$-th configuration
occupies the time interval $[j, j + 1)$, the counter values being the numbers of copies of two letters there, and equal
counter values in consecutive configurations are enforced by matching each letter with one exactly one time unit later. A
timed automaton accepts exactly the timed words that fail to encode a computation visiting the initial instruction
infinitely often, and the existence of such a recurring computation is $\Sigma^1_1$-hard.

Consequently, deciding $L(\mathcal{A}_1) \subseteq L(\mathcal{A}_2)$ for timed Büchi automata is $\Pi^1_1$-hard as well, by
taking for $\mathcal{A}_1$ an automaton that accepts every timed word.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)
- [Timed words and timed languages](timed-words-and-timed-languages.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Lemma 5.1, Theorem 5.2 and its proof, and Corollary 5.3 (inclusion).
