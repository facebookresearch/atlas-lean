# The emptiness problem for probabilistic automata is undecidable

There is no algorithm that decides, given a [probabilistic automaton](probabilistic-automata-and-cut-point-languages.md) $\mathcal{A}$ and a cut-point $\lambda$,
whether some word $w$ has $P_{\mathcal{A}}(w) \ge \lambda$ (Paz); the same holds for the strict version $P_{\mathcal{A}}(w) > \lambda$, already for automata whose
transition probabilities lie in $\{0, 1/2, 1\}$. Emptiness becomes decidable, and PSPACE-complete, for automata with a single
probabilistic transition, and stays undecidable for automata with two.

## Depends on

- [Probabilistic automata and cut-point languages](probabilistic-automata-and-cut-point-languages.md)

## Expansion

This page becomes ready once:

- Undecidability of the equality problem for probabilistic automata (Bertoni), from which the cited proof reduces (proof prerequisite; not yet stated)

## Sources

- H. Gimbert and Y. Oualhadj, "Probabilistic automata on finite words: decidable and undecidable problems", *Proceedings of ICALP 2010*, Lecture Notes in Computer Science 6199, Springer, 2010 (version <https://hal.science/hal-00456538v2>): Section 2, Definition 2 (simple automata), Proposition 1 (Bertoni), Proposition 2, Theorem 1 (Paz), and Propositions 3–5.
