# Universality of one-clock timed automata with silent transitions or Büchi acceptance is undecidable

Universality of nondeterministic timed automata with a single clock is decidable over finite timed words, but becomes undecidable once
silent transitions are allowed, and also over infinite timed words with Büchi acceptance.

**Theorem (Lasota and Walukiewicz).**

1. The universality problem for one-clock nondeterministic [timed automata over finite timed words](timed-automata-over-finite-timed-words.md) with
   $\varepsilon$-transitions is undecidable. Here a timed word over $\Sigma$ is accepted if some timed word over $\Sigma \cup \{\varepsilon\}$, accepted by the automaton read
   over the alphabet $\Sigma \cup \{\varepsilon\}$, yields it when its $\varepsilon$-letters are erased.
2. The universality problem for one-clock nondeterministic [timed Büchi automata](../timed-buchi-automata.md) over infinite timed words is undecidable.

Consequently, emptiness is undecidable for one-clock alternating timed automata over infinite words with Büchi acceptance. In contrast, over finite timed
words emptiness of one-clock alternating timed automata without silent transitions is decidable, though not primitive recursive, and the same lower bound
holds for universality of one-clock nondeterministic timed automata.

## Depends on

- [Timed automata over finite timed words](timed-automata-over-finite-timed-words.md)
- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

For item 1, the proof reduces reachability for perfect channel systems, which is undecidable for channel alphabets with at least two letters (Brand and Zafiropulo): it builds a one-clock automaton with $\varepsilon$-transitions accepting exactly the timed words that are not encodings of perfect computations ending in
the target configuration. For item 2, the proof
reduces the halting problem of a deterministic Turing machine started on the empty tape, modified so that after accepting it clears its tape and restarts; the
machine halts exactly when it has an infinite, repeatedly accepting computation, which is encoded as a timed $\omega$-word, and a one-clock Büchi automaton accepts
exactly the timed $\omega$-words that do not encode such a computation.

## Sources

- S. Lasota and I. Walukiewicz, "Alternating timed automata", *ACM Transactions on Computational Logic* 9(2), article 10, 27 pages, 2008, doi:10.1145/1342991.1342994; conference version in *Foundations of Software Science and Computation Structures (FoSSaCS 2005)*, Lecture Notes in Computer Science 3441, pp. 250–265, 2005, doi:10.1007/978-3-540-31982-5_16. Read in arXiv:cs/0512031v2: the undecidability theorem of the section "Silent transitions" with its definitions and the cited theorem on perfect channel systems, the theorem of the section "Infinite words" with its corollary, and the decidability theorem and lower bound of the sections "Decidability" and "Lower Bound".
