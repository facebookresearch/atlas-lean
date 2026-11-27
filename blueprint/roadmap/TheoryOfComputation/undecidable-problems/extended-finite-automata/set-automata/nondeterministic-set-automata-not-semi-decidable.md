# Universality, equivalence, inclusion and regularity of nondeterministic set automata are not semi-decidable

For nondeterministic set automata, no algorithm even semi-decides whether one accepts every word, whether it is equivalent to a given regular set or to another such automaton, whether one language is included in another, whether its language is regular, or whether it is accepted by some deterministic set automaton.

Let set automata, deterministic (DSA) and nondeterministic (NSA), be as in [Set automata](set-automata.md), and let $\mathsf{DSA}$ be the class of languages accepted by deterministic set automata.

**Theorem (Kutrib, Malcher and Wendlandt).** For nondeterministic set automata the following questions are not semi-decidable: universality, equivalence with a given regular set, equivalence of two automata, inclusion of the language of one in that of another, and regularity of the language. Moreover it is not semi-decidable whether the language accepted by a given NSA belongs to $\mathsf{DSA}$ (Theorem 3 of the copy read, citing Kutrib, Malcher and Wendlandt).

In particular all these problems are undecidable. Emptiness of nondeterministic set automata is decidable, in polynomial space, and it is PSPACE-complete for deterministic ones (Rubtsov and Vyalyi).

## Depends on

- [Set automata](set-automata.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The copy read explains that these results rest on the fact that nondeterministic set automata can accept the set of invalid computations of a Turing machine. That set is universal exactly when the machine has no accepting computation, which is not semi-decidable; the remaining questions are handled in the original paper of Kutrib, Malcher and Wendlandt. The construction accepting invalid computations has no page.

## Sources

- M. Kutrib, A. Malcher and M. Wendlandt, "Set automata", International Journal of Foundations of Computer Science 27 (2016), no. 2, 187–214, https://doi.org/10.1142/S0129054116400062 (cited beside the paper below, which restates the result).
- A. A. Rubtsov and M. N. Vyalyi, "On computational complexity of set automata", Information and Computation 281 (2021), article 104797, https://doi.org/10.1016/j.ic.2021.104797; read in arXiv:1704.03730v2 (Theorem 3 and the sentence before it in Section 1.1 of arXiv:1704.03730v2, and the abstract for the emptiness bounds).
