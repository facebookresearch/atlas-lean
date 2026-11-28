# Universality of one-clock timed automata with silent transitions or Büchi acceptance is undecidable

Universality of nondeterministic timed automata with a single clock is decidable over finite timed words, but becomes undecidable once
silent transitions are allowed, and also over infinite timed words with Büchi acceptance.

**Theorem (Lasota and Walukiewicz).**

1. The universality problem for one-clock nondeterministic [timed automata over finite timed words](timed-automata-over-finite-timed-words.md) with
   $\varepsilon$-transitions is undecidable. Here a timed word over $\Sigma$ is accepted if some timed word over $\Sigma \cup \{\varepsilon\}$, accepted by the automaton read
   over the alphabet $\Sigma \cup \{\varepsilon\}$, yields it when its $\varepsilon$-letters are erased.
2. The universality problem for one-clock nondeterministic [timed Büchi automata](../timed-buchi-automata.md) over infinite timed words is undecidable.

The source uses its own timed words (Section 2 and Section 6): a finite timed word is a sequence $(a_1, t_1) \cdots (a_n, t_n)$ of letters with nonnegative delays (so several letters may occur at the same time), clock constraints compare a clock with a nonnegative integer, and a timed $\omega$-word has strictly increasing time stamps $t_1 < t_2 < \cdots$ with no condition that time diverges. The linked pages use positive delays and unbounded time stamps respectively; the theorem is meant in the source's conventions.

Consequently, emptiness is undecidable for one-clock alternating timed automata over infinite words with Büchi acceptance. In contrast, over finite timed
words emptiness of one-clock alternating timed automata without silent transitions is decidable, though not primitive recursive, and the same lower bound
holds for universality of one-clock nondeterministic timed automata.

## Depends on

- [Timed automata over finite timed words](timed-automata-over-finite-timed-words.md)
- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

For item 1, the proof reduces reachability for perfect channel systems, which is undecidable for channel alphabets with at least two letters (Brand and Zafiropulo): it builds a one-clock automaton with $\varepsilon$-transitions accepting exactly the timed words that are not encodings of perfect computations ending in
the target configuration. For item 2, the proof
reduces the halting problem of a deterministic Turing machine started on the empty tape, modified so that after accepting it clears its tape and restarts; the
machine halts exactly when it has an infinite, repeatedly accepting computation, which is encoded as a timed $\omega$-word, and a one-clock Büchi automaton accepts
exactly the timed $\omega$-words that do not encode such a computation. A complete expansion links a page for the undecidability of reachability in perfect channel systems over at least two letters (Brand and Zafiropulo; Theorem 6 as cited in the source), the result item 1 starts from. The linked halting result is for some machine on its inputs; item 2 needs halting from the empty tape (proof of Theorem 7 of the source), and a good expansion also links a page for that form.

## Sources

- S. Lasota and I. Walukiewicz, "Alternating timed automata", *ACM Transactions on Computational Logic* 9(2), article 10, 27 pages, 2008, doi:10.1145/1342991.1342994; conference version in *Foundations of Software Science and Computation Structures (FoSSaCS 2005)*, Lecture Notes in Computer Science 3441, pp. 250–265, 2005, doi:10.1007/978-3-540-31982-5_16. Read in arXiv:cs/0512031v2: Theorem 5 in Section 5 ("Silent transitions") with Definitions 11 and 12 and the cited Theorem 6 on perfect channel systems, Theorem 7 in Section 6 ("Infinite words") with the remark after it, and Theorem 2, Theorem 3 and Corollary 2 of Sections 3 ("Decidability") and 4 ("Lower Bound"), with the numbering of that version.
